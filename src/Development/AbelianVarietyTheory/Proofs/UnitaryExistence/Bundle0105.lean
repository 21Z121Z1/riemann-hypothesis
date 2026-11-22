import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponent
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

namespace DefiniteData

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_std (x y : Fin r → E) :
    herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]

theorem emb_herm_self (φ : E →+* ℂ) (x : Fin r → E) :
    φ (herm (1 : Matrix (Fin r) (Fin r) E) x x) = ((∑ a, ‖φ (x a)‖ ^ 2 : ℝ) : ℂ) := by
  rw [herm_std, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

def stdLat (E : Type) [Field E] [NumberField E] (r : ℕ) : Submodule (𝓞 E) (Fin r → E) :=
  LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin r))

omit [IsCMField E] in
theorem mem_stdLat (x : Fin r → E) : x ∈ stdLat E r ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · rintro ⟨y, rfl⟩ a
    exact (y a).isIntegral_coe
  · intro h
    exact ⟨fun a => ⟨x a, h a⟩, rfl⟩

omit [IsCMField E] in
theorem single_mem_stdLat (b : Fin r) : (Pi.single b 1 : Fin r → E) ∈ stdLat E r := by
  rw [mem_stdLat]
  intro a
  by_cases h : a = b
  · subst h; simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

theorem stab_finite :
    {γ : GL (Fin r) E | IsUStab (1 : Matrix (Fin r) (Fin r) E) (stdLat E r) γ}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le (K := E) (A := ℂ) 1
  have hpi := Set.Finite.pi' (fun _ : Fin r => Set.Finite.pi' (fun _ : Fin r => hfin))
  refine Set.Finite.of_finite_image (hpi.subset ?_) ?_
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
  · rintro _ ⟨γ, ⟨hh, hl⟩, rfl⟩ a b
    have hv : ∀ i, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single b 1) i =
        (γ : Matrix (Fin r) (Fin r) E) i b := by
      intro i; simp
    refine ⟨?_, fun φ => ?_⟩
    · have := (mem_stdLat _).1 ((hl _).1 (single_mem_stdLat b)) a
      rwa [hv] at this
    · have h1 := congrArg φ (hh (Pi.single b 1) (Pi.single b 1))
      rw [emb_herm_self, emb_herm_self] at h1
      have h2 := Complex.ofReal_injective h1
      have h3 : ∑ i, ‖φ ((Pi.single b 1 : Fin r → E) i)‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro i _ hi; simp [hi]
        · simp
      rw [h3] at h2
      simp only [hv] at h2
      have h4 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2 ≤ 1 := by
        rw [← h2]
        exact Finset.single_le_sum (f := fun i => ‖φ ((γ : Matrix (Fin r) (Fin r) E) i b)‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ a)
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
  · intro γ _ δ _ h
    apply Units.ext
    ext a b
    exact congrFun (congrFun h a) b

theorem eq_zero_of_herm_self {x : Fin r → E}
    (h : herm (1 : Matrix (Fin r) (Fin r) E) x x = 0) : x = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := emb_herm_self φ x
  rw [h, map_zero] at h1
  have h2 : ∑ a, ‖φ (x a)‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  funext a
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h2 a (Finset.mem_univ a)
  have h4 : φ (x a) = 0 := by simpa using h3
  exact (map_eq_zero_iff φ φ.injective).1 h4

theorem nonempty_data (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) :
    Nonempty (FD.Data E r) := by
  classical
  let X : FD.Data E 1 := inhab
  exact ⟨
  { Ψ := X.Ψ
    cmType := X.cmType
    Gm := 1
    Gm_herm := by
      intro a b
      by_cases h : a = b
      · subst h; simp [cc_one]
      · simp [h, Ne.symm h, cc_zero]
    Gm_det := by simp
    p0 := r
    p0_le := le_rfl
    signature := by
      intro τ
      refine ⟨1, by simp, ?_⟩
      ext a b
      by_cases h : a = b
      · subst h
        simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite]
      · simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite, h, Ne.symm h]
    Λ := stdLat E r
    Λ_fg := by
      unfold stdLat
      rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    Λ_span := by
      rw [eq_top_iff]
      intro x _
      rw [pi_eq_sum_univ' x]
      exact Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat b))
    den := 1
    den_ne := one_ne_zero
    Λ_int := by
      intro x hx y hy
      rw [herm_std, show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
      exact IsIntegral.sum _ fun a _ =>
        ((mem_stdLat x).1 hx a).mul (isIntegral_cc ((mem_stdLat y).1 hy a))
    Γ := ⊥
    Γ_stab := by
      intro γ hγ
      rw [Subgroup.mem_bot] at hγ
      subst hγ
      simp [IsUStab]
    Γ_index := ⟨(stab_finite (E := E) (r := r)).toFinset, fun γ hγ =>
      ⟨γ, (Set.Finite.mem_toFinset _).2 hγ, by simp⟩⟩
    Γ_free := fun γ hγ _ _ _ _ _ => Subgroup.mem_bot.mp hγ
    χ := fun _ _ => 1
    χ_mul := by intros; simp
    χ_add := by intros; simp
    χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
    ξ0 := X.ξ0
    ξ0_im := X.ξ0_im
    ξ0_ne := X.ξ0_ne
    κ0 := X.κ0
    κ0_xi := X.κ0_xi
    κ0_sign := X.κ0_sign
    m := 1
    m_pos := one_pos
    transv := by
      intro ξ _ hiso s _ _
      have hξ := eq_zero_of_herm_self hiso
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      simp [transvMat, hξ, Matrix.one_apply] }⟩

end DefiniteData

theorem exists_unf_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Nonempty U.Comp := by
  intro E _ _ _ H Dw l Xo c h σ
  obtain ⟨X⟩ := DefiniteData.nonempty_data E (Dw.p + Dw.q)
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist E H Dw l Xo c h σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨()⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.MarkUniq

lemma nsmul_cancel (F : Type) [Field F] {M : Type} [AddCommGroup M] [Module F M] {N : ℕ} (hN : (N : F) ≠ 0)
    {x y : M} (h : N • x = N • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  exact smul_right_injective _ hN h

lemma sub_eq_nsmul_sub {M : Type} [AddCommGroup M] {N : ℕ} {x y z w w' : M} (h : x - z = N • w) (h' : y - z = N • w') :
    x - y = N • (w - w') := by
  rw [smul_sub, ← h, ← h']; abel

lemma exists_of_finVec_eq_nsmul {D : D7} (V : HSp D) (g : GA D V) (N : ℕ) (hN : N ≠ 0)
    (u : Fin V.rank → D.host.E) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ latGHat V g)
    (h : finVec V u = N • w) : ∃ x ∈ latG V g, u = N • x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V g
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hu : u = N • ((N : D.host.E)⁻¹ • u) := by
    rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  refine ⟨(N : D.host.E)⁻¹ • u, ?_, hu⟩
  refine ((GlobalTheory.T.adelicCompletion_rational_points_and_approximation D.host.F D.host.E V.rank (latG V g) h1 h2).1 _).1 ?_
  have e : N • finVec V ((N : D.host.E)⁻¹ • u) = N • w := by
    rw [← h]
    conv_rhs => rw [hu]
    funext i
    simp only [finVec, Pi.smul_apply]
    exact (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) N _).symm
  have e' := nsmul_cancel D.host.F hNF e
  rw [h5, ← e'] at hw
  exact hw

lemma finVec_sub {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    finVec V (u - v) = finVec V u - finVec V v := by
  funext i
  simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]

lemma half_surj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (t : A →ₗ[𝓞 E] B) (ht : ∀ b, ∃ a e, b = t a + l.M • e) (b : B)
    (hb : b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) B)) :
    ∃ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) A), ∃ e, b = t a + l.M • e := by
  obtain ⟨a, e, hae⟩ := ht b
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have h2 : x • b ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) B) := by
    rw [← l.prod, mul_smul]
    exact Submodule.smul_mem_smul hx hb
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨e', -, he'⟩ := h2
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, e' + y • e, ?_⟩
  rw [Nat.cast_smul_eq_nsmul] at he'
  have : b = x • b + y • b := by rw [← add_smul, hxy, one_smul]
  rw [this, ← he', map_smul, smul_add, smul_comm l.M y e]
  conv_lhs => rw [hae]
  rw [smul_add]
  abel

lemma matched {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} (C : Ctx Xo c σ V V.rank) (h : GA D V) (k k' : Fin C.F.n)
    (γ γ' : GA D V) (hm : C.Mark h k γ) (hm' : C.Mark h k' γ') :
    ∃ δ : GL (Fin V.rank) D.host.E, IsRat V (γ' * γ⁻¹) δ ∧
      (∀ v, v ∈ (C.M.X k).Λ ↔ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ (C.M.X k').Λ) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ (C.M.X k').Λ,
          (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) =
            (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) + l.M • w := by
  obtain ⟨r1, -, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨hγ, hΛ, hk⟩ := hm
  obtain ⟨hγ', hΛ', hk'⟩ := hm'
  obtain ⟨δ, hδ⟩ := (r1 _).1 ((GQ V).mul_mem hγ' ((GQ V).inv_mem hγ))
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 _ δ (γ * h) hδ
  have hg : γ' * γ⁻¹ * (γ * h) = γ' * h := by group
  rw [hg] at m1 m2
  have hL : (C.M.X k).Λ = latG V (γ * h) := SetLike.ext' (hΛ.trans (Set.image_id _))
  have hL' : (C.M.X k').Λ = latG V (γ' * h) := SetLike.ext' (hΛ'.trans (Set.image_id _))
  refine ⟨δ, hδ, fun v => by rw [hL, hL']; exact m1 v, fun a ha => ?_⟩
  obtain ⟨w, hw, e⟩ := hk a ha
  obtain ⟨w', hw', e'⟩ := hk' a ha
  change finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _ at e
  change finVec V (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) - _ = _ at e'
  have e2 := congrArg (fun z => (finHom V (γ' * γ⁻¹)).1 *ᵥ z) e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
  rw [(r5 _ δ hδ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hg] at e2
  obtain ⟨x, hx, hx'⟩ := exists_of_finVec_eq_nsmul V (γ' * h) l.M (by have := l.three_le; omega)
    ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
      (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E)) ((finHom V (γ' * γ⁻¹)).1 *ᵥ w - w')
    (sub_mem ((m2 w).1 hw) hw') ((finVec_sub V _ _).trans (sub_eq_nsmul_sub e2 e'))
  exact ⟨x, hL' ▸ hx, by rw [← hx']; abel⟩

theorem mark_unique : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h, (∀ k k' γ γ', C.Mark h k γ → C.Mark h k' γ' → k = k') ∧ ∀ k γ γ', C.Mark h k γ → C.Mark h k γ' → ∃ δ ∈ (C.M.X k).Γ, C.fr (γ' * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, r2, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  have hG : ∀ k, (C.M.X k).Gm = -V.gramᵀ := fun k => (hC.modelW k).1
  refine ⟨fun k k' γ γ' hm hm' => ?_, fun k γ γ' hm hm' => ?_⟩
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k' γ γ' hm hm'
    refine GlobalTheory.ClassUniq.eq_of_matched GlobalTheory.T.thetaUniformisation_complexAbelianVariety GlobalTheory.firstFiveLaws.1 _ H Dw l Xo _ C.g _ C.F _ C.M k k' δ
      hC.pos hC.good ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hC.good).2.2.2 Dw C.g C.e) hC.base
      ((hG k').trans (hG k).symm) ((hC.modelW k').2.trans (hC.modelW k).2.symm)
      (by rw [hG k]; exact r2 _ δ hδ) hΛ hmk (fun a => ?_)
    refine ⟨_ - _, sub_mem ((hΛ _).1 (C.M.φ k (C.F.t k a)).2) (C.M.φ k' (C.F.t k' a)).2, ?_⟩
    rw [hC.lA, one_smul]; abel
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k γ γ' hm hm'
    have hφ : ∀ w ∈ (C.M.X k).Λ, ∃ b, (C.M.φ k b : Fin V.rank → D.host.E) = w := fun w hw =>
      ⟨(C.M.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
    refine ⟨δ, (hC.base.gam k δ).2 ⟨⟨by rw [hG k]; exact r2 _ δ hδ, hΛ⟩, fun b hb => ?_, fun a => ?_⟩, ?_⟩
    · have hM : l.M' = l.M := by rw [Level.M', hC.lA, Nat.lcm_one_right]
      obtain ⟨a, ha, e, rfl⟩ := half_surj l (C.F.t k) (fun b => hM ▸ C.F.t_surj k b) b hb
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      obtain ⟨b', hb'⟩ := hφ _ (sub_mem (add_mem hw ((hΛ _).1 (C.M.φ k e).2)) (C.M.φ k e).2)
      refine ⟨b', ?_⟩
      rw [hb', map_add, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul, Matrix.mulVec_add,
        Matrix.mulVec_smul, hw', smul_sub, smul_add]
      abel
    · obtain ⟨b', hb'⟩ := hφ _ (sub_mem ((hΛ _).1 (C.M.φ k a).2) (C.M.φ k a).2)
      refine ⟨b', ?_⟩
      rw [hb', hC.lA, one_smul]; abel
    · funext τ
      have hg : γ' * h = γ' * γ⁻¹ * (γ * h) := by group
      have e := ((GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf).1 τ.1).2.1 (γ' * γ⁻¹) (γ * h)
      rw [← hg, (r5 _ δ hδ).2 τ.1 _ (hC.inf τ.1)] at e
      change archM V (C.θ τ.1) (γ' * h) * C.x₀ τ.1 =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [e, Matrix.mul_assoc]

end GlobalTheory.MarkUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.NormUnBor

theorem diag_ne_zero {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.det ≠ 0)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (j : Fin g) : A j j ≠ 0 := by
  have hdet : A.det = ∏ i, A i i := by
    rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin g))]
    · simp
    · intro s _ hs
      by_contra hne
      have hp : ∏ i, A (s i) i ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
      have hall : ∀ i, A (s i) i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)
      have hsum : ∑ i, ((e (s i)).2 : ℕ) = ∑ i, ((e i).2 : ℕ) :=
        Equiv.sum_comp s (fun i => ((e i).2 : ℕ))
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => (htri _ _ (hall i)).2)).1 hsum
      apply hs
      ext i
      have h1 := (htri _ _ (hall i)).1
      have h2 := heq i (Finset.mem_univ i)
      have : e (s i) = e i := Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
      simp [e.injective this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdet] at hA
  exact Finset.prod_ne_zero_iff.1 hA j (Finset.mem_univ j)

theorem col_eq_sum {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (τ : T) (i : Fin (m τ)) :
    ∑ i' : Fin (m τ), A (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) (1 : ℂ) : Fin g → ℂ) =
      A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 := by
  funext p
  obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective p
  rw [Matrix.mulVec_single_one, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single i']
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      exact hj (sigma_mk_injective (β := fun τ => Fin (m τ)) (e.symm.injective h)).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h0 : A (e.symm ⟨τ', i'⟩) (e.symm ⟨τ, i⟩) = 0 := by
      by_contra hne
      have := (htri _ _ hne).1
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact hτ this
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hτ (congrArg Sigma.fst (e.symm.injective h))

theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    (normConst ty ξ₀ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (div_pos (by positivity) ?_)).ne'
  exact Finset.prod_pos fun j _ => mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 h))

theorem normUn_bor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hG hB hN hU x b hb h
  obtain ⟨h₀, hdet, hP, htri, -, -, hw⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k T.Pf T.per x.1 x.2 b hb
  obtain ⟨κ, hκ, hy⟩ := hU x
  obtain ⟨κ', hκ', hy'⟩ := hU ⟨_, h⟩
  have hx : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using x.2
  have hx' : T.co.symm (rmul x.1 b) ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using h
  obtain ⟨hxx, hder, t₀, hsec, ht₀⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hx _ hx' κ κ' _ _
    (LinearEquiv.refl _ _) h₀ hy hy'
    ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
    (fun a => by
      simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.refl_apply]
      exact hP a)
  have hsq : toC (t₀ : CAt σ) ^ 2 * h₀.det = 1 := by
    have hc := normConst_ne_zero (fun j => relab c σ (e j).1) (M.X k).ξ0_ne
    have h1 := (T.norm _ hx).1.ne_zero
    have h2 := (T.norm _ hx').1.ne_zero
    rw [hκ, hκ'] at ht₀
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc h1) h2)
    linear_combination ht₀
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := diag_ne_zero e h₀⁻¹ hinv htri
  let d : Fin g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (e.symm p))
  refine ⟨t, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [e.apply_symm_apply, e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy.1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (T.isPer _ hx) _ _ _ (hy.2.1 τ) _ _).2 ?_
    rw [col_eq_sum e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hsec
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n hD
    rw [← hw un a n (toC (t₀ : CAt σ)) hD.2 hsq]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) = _
    rw [Fintype.prod_option, mul_comm]
    congr 1
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (e.symm (e j)) (e.symm (e j)) ^ a ((e j).1, (e j).2) = _
    rw [e.symm_apply_apply]

end GlobalTheory.NormUnBor
end

