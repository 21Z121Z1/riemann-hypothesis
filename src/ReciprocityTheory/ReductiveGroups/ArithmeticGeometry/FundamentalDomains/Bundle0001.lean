import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainTranslate
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate

open MeasureTheory Complex
open scoped Pointwise

variable {ι : Type} [Fintype ι]

theorem fd_translate (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (f : (ι → ℝ) → ℂ) (hf : ∀ p ∈ L, ∀ s, f (p + s) = f s)
    (v : ι → ℝ) : ∫ s in D, f (v + s) = ∫ s in D, f s := by
  have hv : IsAddFundamentalDomain L (v +ᵥ D) volume := hD.vadd_of_comm v
  have h1 : ∫ s in D, f (v + s) = ∫ s in v +ᵥ D, f s := by
    have := (measurePreserving_add_left (volume : Measure (ι → ℝ)) v).setIntegral_image_emb
      (measurableEmbedding_addLeft v) f D
    rw [← this]
    rfl
  rw [h1]
  exact hv.setIntegral_eq hD (fun p s => hf p.1 p.2 s)

theorem orth (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (μ : ι → ℝ) (hμ : ∀ p ∈ L, ∃ k : ℤ, 2 * ∑ i, μ i * p i = k) :
    ∫ s in D, cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) =
      if μ = 0 then ((volume D).toReal : ℂ) else 0 := by
  split_ifs with h0
  · subst h0
    simp [Measure.real]
  · obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (funext h)
    classical
    set e : (ι → ℝ) → ℂ := fun s => cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) with he
    have hadd : ∀ v s : ι → ℝ,
        e (v + s) = cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) * e s := by
      intro v s
      simp only [he, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib,
        Complex.exp_add]
    have hinv : ∀ p ∈ L, ∀ s, e (p + s) = e s := by
      intro p hp s
      obtain ⟨k, hk⟩ := hμ p hp
      rw [hadd]
      have hk' : (2 : ℂ) * ∑ i, (μ i : ℂ) * (p i : ℂ) = k := by exact_mod_cast hk
      have h2 : 4 * (Real.pi : ℂ) * I * ∑ i, (μ i : ℂ) * (p i : ℂ) = k * (2 * Real.pi * I) := by
        linear_combination (2 * (Real.pi : ℂ) * I) * hk'
      rw [h2, Complex.exp_int_mul_two_pi_mul_I, one_mul]

    let v : ι → ℝ := Pi.single j (1 / (4 * μ j))
    have hsumR : ∑ i, μ i * v i = 1 / 4 := by
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [v, Pi.single_apply, hi]) (by simp)]
      simp only [v, Pi.single_eq_same]
      field_simp
    have hsum : ∑ i, (μ i : ℂ) * (v i : ℂ) = 1 / 4 := by
      have h := congrArg Complex.ofReal hsumR
      push_cast at h
      exact h
    have hexp : cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) = -1 := by
      rw [hsum]
      have h3 : 4 * (Real.pi : ℂ) * I * (1 / 4) = Real.pi * I := by ring
      rw [h3, Complex.exp_pi_mul_I]
    have htr := fd_translate L D hD e hinv v
    simp only [hadd, hexp, neg_one_mul, integral_neg] at htr
    linear_combination (-1 / 2 : ℂ) * htr

end ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open Complex
open scoped ComplexConjugate InnerProductSpace

theorem onb_perp (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ℂ) (hα : α ≠ 0) :
    ∃ g : Fin (n - 1) → Fin n → ℂ,
      (∀ k l, ∑ a, g k a * conj (g l a) = if k = l then 1 else 0) ∧
      (∀ k, ∑ a, g k a * conj (α a) = 0) ∧
      (∀ γ : Fin n → ℂ, ∑ a, γ a * conj (α a) = 0 → γ ∈ Submodule.span ℂ (Set.range g)) := by
  classical
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 α
  have hv : v ≠ 0 := by
    intro h
    apply hα
    have h' := congrArg WithLp.ofLp h
    simpa [v] using h'
  haveI : Fact (Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  have hK : Module.finrank ℂ (ℂ ∙ v)ᗮ = n - 1 := Submodule.finrank_orthogonal_span_singleton hv
  let b : OrthonormalBasis (Fin (n - 1)) ℂ (ℂ ∙ v)ᗮ :=
    (stdOrthonormalBasis ℂ (ℂ ∙ v)ᗮ).reindex (finCongr hK)
  refine ⟨fun k a => ((b k : (ℂ ∙ v)ᗮ) : EuclideanSpace ℂ (Fin n)).ofLp a, ?_, ?_, ?_⟩
  · intro k l
    have h := (orthonormal_iff_ite.mp b.orthonormal) l k
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [dotProduct, Pi.star_apply, RCLike.star_def] at h
    rw [h]
    exact if_congr eq_comm rfl rfl
  · intro k
    have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b k).2
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct, v] using h
  · intro γ hγ
    have hw : (WithLp.toLp 2 γ : EuclideanSpace ℂ (Fin n)) ∈ (ℂ ∙ v)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_eq_star_dotProduct]
      simpa [dotProduct, v] using hγ
    have hsum := b.sum_repr' ⟨_, hw⟩
    have hγeq : γ = ∑ i, inner ℂ (b i) (⟨_, hw⟩ : (ℂ ∙ v)ᗮ) •
        (fun a => ((b i : (ℂ ∙ v)ᗮ) : EuclideanSpace ℂ (Fin n)).ofLp a) := by
      funext a
      have h := congrArg (fun x : (ℂ ∙ v)ᗮ => ((x : EuclideanSpace ℂ (Fin n))).ofLp a) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      rw [Finset.sum_apply]
      simpa using h.symm
    rw [hγeq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma
section
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma

open Complex Filter Function Function.Periodic Metric Set
open scoped Topology Real

theorem periodic_schwarz {g : ℂ → ℂ} {M T t B : ℝ} (hM : 0 < M) (ht : 0 < t) (htT : t < T)
    (hper : Periodic g M) (hdiff : ∀ z : ℂ, -T < z.im → DifferentiableAt ℂ g z)
    (hzero : Tendsto g (comap im atTop) (𝓝 0)) (hB : ∀ z : ℂ, z.im = -t → ‖g z‖ ≤ B) :
    ‖g 0‖ ≤ Real.exp (-2 * π * t / M) * B := by
  have hM0 : (M : ℝ) ≠ 0 := hM.ne'
  have hT : 0 < T := ht.trans htT
  set F := cuspFunction M g with hF
  set R := Real.exp (2 * π * t / M) with hRdef
  have hR : 0 < R := Real.exp_pos _
  have h1R : 1 < R := by
    have := Real.exp_lt_exp.2 (show (0 : ℝ) < 2 * π * t / M by positivity)
    rw [Real.exp_zero] at this
    rw [hRdef]
    exact this
  have hF0 : F 0 = 0 := cuspFunction_zero_of_zero_at_inf hM hzero
  have hdiffF : DifferentiableOn ℂ F (closedBall 0 R) := by
    intro q hq
    apply DifferentiableAt.differentiableWithinAt
    by_cases hq0 : q = 0
    · subst hq0
      have hev : ∀ᶠ z : ℂ in comap im atTop, 0 ≤ z.im :=
        tendsto_comap.eventually (eventually_ge_atTop 0)
      exact differentiableAt_cuspFunction_zero hM hper
        (hev.mono fun z hz => hdiff z (by linarith)) (hzero.isBigO_one ℝ)
    · rw [← qParam_right_inv hM0 hq0]
      apply differentiableAt_cuspFunction hM0 hper
      apply hdiff
      have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq0
      have hqR : ‖q‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hq
      have hlog : Real.log ‖q‖ ≤ 2 * π * t / M := by
        calc Real.log ‖q‖ ≤ Real.log R := Real.log_le_log hqn hqR
          _ = 2 * π * t / M := by rw [hRdef, Real.log_exp]
      have key : M / (2 * π) * Real.log ‖q‖ ≤ t := by
        calc M / (2 * π) * Real.log ‖q‖ ≤ M / (2 * π) * (2 * π * t / M) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = t := by field_simp
      rw [im_invQParam]
      have : -M / (2 * π) * Real.log ‖q‖ = -(M / (2 * π) * Real.log ‖q‖) := by ring
      rw [this]
      linarith
  have hdsl : DifferentiableOn ℂ (dslope F 0) (closedBall 0 R) :=
    (differentiableOn_dslope (closedBall_mem_nhds 0 hR)).2 hdiffF
  have hdc : DiffContOnCl ℂ (dslope F 0) (ball 0 R) :=
    hdsl.diffContOnCl_ball subset_rfl
  have hfront : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖dslope F 0 z‖ ≤ B / R := by
    intro z hz
    rw [frontier_ball 0 hR.ne', mem_sphere_zero_iff_norm] at hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; exact hR.ne' hz.symm
    rw [dslope_of_ne _ hz0, slope_def_field, hF0, sub_zero, sub_zero, norm_div, hz]
    apply div_le_div_of_nonneg_right _ hR.le
    rw [hF, cuspFunction_eq_of_nonzero _ _ hz0]
    apply hB
    rw [im_invQParam, hz, hRdef, Real.log_exp]
    field_simp
  have h1 : (1 : ℂ) ∈ closure (ball (0 : ℂ) R) :=
    subset_closure (by simpa [mem_ball, dist_zero_right] using h1R)
  have hmain := norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hfront h1
  have hq1 : qParam M 0 = 1 := by simp [qParam]
  have hg0 : g 0 = dslope F 0 1 := by
    rw [dslope_of_ne _ one_ne_zero, slope_def_field, hF0, sub_zero, sub_zero, div_one,
      ← hq1, hF, eq_cuspFunction hM0 hper]
  rw [hg0]
  calc ‖dslope F 0 1‖ ≤ B / R := hmain
    _ = Real.exp (-2 * π * t / M) * B := by
      rw [hRdef, show -2 * π * t / M = -(2 * π * t / M) by ring, Real.exp_neg, div_eq_mul_inv,
        mul_comm]

end ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def cc (x : E) : E := IsCMField.complexConj E x

def herm {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : E :=
  ∑ a, ∑ b, x a * G a b * cc (y b)

def hermC {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) : ℂ :=
  ∑ a, ∑ b, u a * τ (G a b) * conj (v b)

def col {r : ℕ} (x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : Fin r → ℂ := fun k => x k a

def gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => hermC τ G (col x a) (col x b)

def lminor {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) : ℂ :=
  (M.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det

def sgn (p0 a : ℕ) : ℝ := if a < p0 then 1 else -1

def psgn (p0 i : ℕ) : ℝ := ∏ a ∈ Finset.range i, sgn p0 a

abbrev Frame (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Type := Ψ → Fin r → Fin r → ℂ

def mat {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) (τ : Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of (x τ)

def dmin {Ψ : Finset (E →+* ℂ)} {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (τ : Ψ)
    (i : Fin (r + 1)) : ℂ :=
  lminor (gram τ.1 G (mat x τ)) i

def GG (Ψ : Finset (E →+* ℂ)) {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) : Set (Frame Ψ r) :=
  {x | ∀ τ : Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn p0 i * (dmin G x τ i).re}

def Bor (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Set (Frame Ψ r) :=
  {b | ∀ τ : Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0}

def rmul {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x b : Frame Ψ r) : Frame Ψ r :=
  fun τ => (mat x τ * mat b τ : Matrix (Fin r) (Fin r) ℂ)

def lact {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x : Frame Ψ r) : Frame Ψ r :=
  fun τ => ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def IsUStab {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (γ : GL (Fin r) E) : Prop :=
  (∀ x y, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x) (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) y) =
    herm G x y) ∧
  ∀ x, x ∈ Λ ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x ∈ Λ

def transvMat {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) (α : E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => (if a = b then 1 else 0) + α * ξ a * ∑ k, G b k * cc (ξ k)

abbrev Wt (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Type := Ψ → Fin r → ℤ

def bchar {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : Wt Ψ r) (b : Frame Ψ r) : ℂ :=
  ∏ τ, ∏ i, b τ i i ^ la τ i

structure Data (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) where

  Ψ : Finset (E →+* ℂ)
  cmType : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ

  Gm : Matrix (Fin r) (Fin r) E
  Gm_herm : ∀ a b, cc (Gm a b) = Gm b a
  Gm_det : Gm.det ≠ 0
  p0 : ℕ
  p0_le : p0 ≤ r

  signature : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
    gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)

  Λ : Submodule (𝓞 E) (Fin r → E)
  Λ_fg : Λ.FG
  Λ_span : Submodule.span E (Λ : Set (Fin r → E)) = ⊤
  den : 𝓞 E
  den_ne : den ≠ 0
  Λ_int : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((den : E) * herm Gm x y)

  Γ : Subgroup (GL (Fin r) E)
  Γ_stab : ∀ γ ∈ Γ, IsUStab Gm Λ γ
  Γ_index : ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ
  Γ_free : ∀ γ ∈ Γ, ∀ x ∈ GG Ψ Gm p0, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1

  χ : Wt Ψ r → GL (Fin r) E → ℂ
  χ_mul : ∀ la, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ la (γ * γ') = χ la γ * χ la γ'
  χ_add : ∀ la la', ∀ γ ∈ Γ, χ (la + la') γ = χ la γ * χ la' γ
  χ_fin : ∀ la, ∃ n : ℕ, 0 < n ∧ ∀ γ ∈ Γ, χ la γ ^ n = 1

  ξ0 : E
  ξ0_im : cc ξ0 = -ξ0
  ξ0_ne : ξ0 ≠ 0

  κ0 : E
  κ0_xi : κ0 = 2 * ξ0 ∨ κ0 = -(2 * ξ0)
  κ0_sign : ∀ τ : Ψ, (τ.1 κ0).im < 0
  m : ℕ
  m_pos : 0 < m
  transv : ∀ ξ ∈ Λ, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
    ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0)

namespace Data

variable {r : ℕ} (X : Data E r)

def c (τ : X.Ψ) : ℝ := 2 * ‖τ.1 X.ξ0‖

abbrev dom : Set (Frame X.Ψ r) := GG X.Ψ X.Gm X.p0

def IsSec (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x

def pnorm (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  ‖P x‖ * ∏ τ, ∏ i : Fin r,
    ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

def gramPos (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (gram τ.1 X.Gm (mat x τ)).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)

def posPart (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : ℝ :=
  (∑ a : Fin X.p0, ∑ b : Fin X.p0,
    hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))).re

def maj (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : ℝ :=
  2 * X.posPart x τ v - (hermC τ.1 X.Gm v v).re

def emb (τ : E →+* ℂ) (v : Fin r → E) : Fin r → ℂ := fun a => τ (v a)

def firstMinimumSq (x : Frame X.Ψ r) : ℝ :=
  sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (emb τ.1 v)}

def la1 (x : Frame X.Ψ r) : ℝ := Real.sqrt (X.firstMinimumSq x)

def tt (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ := 1 / (X.c τ * X.maj x τ (emb τ.1 ξ))

def flowMat (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) -
    I * X.c τ * s * τ.1 (ξ a) * ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))

def flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (X.flowMat ξ τ (s τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)

end Data

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TelescopingWeightedSums
section
namespace ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
open Finset

theorem sum_tele (f : ℕ → ℝ) {p n : ℕ} (hp : p ≤ n) :
    ∑ i ∈ Ico p n, (f (i + 1) - f i) = f n - f p := by
  induction n, hp using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    ring

private lemma sum_sub_lo_mul_bounds_of_nonneg (S : Finset ℕ) (a d : ℕ → ℝ) (lo hi : ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (ha : ∀ i ∈ S, lo ≤ a i ∧ a i ≤ hi) :
    0 ≤ ∑ i ∈ S, (a i - lo) * d i ∧ ∑ i ∈ S, (a i - lo) * d i ≤ (hi - lo) * ∑ i ∈ S, d i := by
  constructor
  · exact Finset.sum_nonneg fun i hi' => mul_nonneg (by linarith [(ha i hi').1]) (hd i hi')
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' =>
      mul_le_mul_of_nonneg_right (by linarith [(ha i hi').2]) (hd i hi')

private lemma sum_sub_lo_mul_bounds_of_nonpos (S : Finset ℕ) (a d : ℕ → ℝ) (lo hi : ℝ)
    (hd : ∀ i ∈ S, d i ≤ 0) (ha : ∀ i ∈ S, lo ≤ a i ∧ a i ≤ hi) :
    (hi - lo) * ∑ i ∈ S, d i ≤ ∑ i ∈ S, (a i - lo) * d i ∧ ∑ i ∈ S, (a i - lo) * d i ≤ 0 := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' =>
      mul_le_mul_of_nonpos_right (by linarith [(ha i hi').2]) (hd i hi')
  · exact Finset.sum_nonpos fun i hi' =>
      mul_nonpos_of_nonneg_of_nonpos (by linarith [(ha i hi').1]) (hd i hi')

theorem wsum_bound {n p : ℕ} (hp : p ≤ n) (ρ : ℕ → ℝ) (hρ : ∀ i ≤ n, 0 < ρ i) (h0 : ρ 0 = 1)
    (hn : ρ n = 1)
    (hmono : ((∀ i, i < p → ρ i ≤ ρ (i + 1)) ∧ ∀ i, p ≤ i → i < n → ρ (i + 1) ≤ ρ i) ∨
      ((∀ i, i < p → ρ (i + 1) ≤ ρ i) ∧ ∀ i, p ≤ i → i < n → ρ i ≤ ρ (i + 1)))
    (a : ℕ → ℝ) (lo hi : ℝ) (ha : ∀ i < n, lo ≤ a i ∧ a i ≤ hi) :
    |∑ i ∈ range n, a i * (Real.log (ρ (i + 1)) - Real.log (ρ i))| ≤
      (hi - lo) * |Real.log (ρ p)| := by
  have hsplit : ∑ i ∈ range n, a i * (Real.log (ρ (i + 1)) - Real.log (ρ i)) =
      ∑ i ∈ range p, (a i - lo) * (Real.log (ρ (i + 1)) - Real.log (ρ i)) +
      ∑ i ∈ Ico p n, (a i - lo) * (Real.log (ρ (i + 1)) - Real.log (ρ i)) +
      lo * ∑ i ∈ range n, (Real.log (ρ (i + 1)) - Real.log (ρ i)) := by
    rw [Finset.sum_range_add_sum_Ico _ hp, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have htot : ∑ i ∈ range n, (Real.log (ρ (i + 1)) - Real.log (ρ i)) = 0 := by
    rw [Finset.sum_range_sub (fun i => Real.log (ρ i)) n, h0, hn]; simp
  have hL : ∑ i ∈ range p, (Real.log (ρ (i + 1)) - Real.log (ρ i)) = Real.log (ρ p) := by
    rw [Finset.sum_range_sub (fun i => Real.log (ρ i)) p, h0]; simp
  have hR : ∑ i ∈ Ico p n, (Real.log (ρ (i + 1)) - Real.log (ρ i)) = - Real.log (ρ p) := by
    rw [sum_tele (fun i => Real.log (ρ i)) hp, hn]; simp
  have haL : ∀ i ∈ range p, lo ≤ a i ∧ a i ≤ hi := fun i hi' =>
    ha i (lt_of_lt_of_le (Finset.mem_range.mp hi') hp)
  have haR : ∀ i ∈ Ico p n, lo ≤ a i ∧ a i ≤ hi := fun i hi' => ha i (Finset.mem_Ico.mp hi').2
  rw [hsplit, htot, mul_zero, add_zero]
  rcases hmono with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have dL : ∀ i ∈ range p, 0 ≤ Real.log (ρ (i + 1)) - Real.log (ρ i) := by
      intro i hi'
      have hip := Finset.mem_range.mp hi'
      have := Real.log_le_log (hρ i (by omega)) (h1 i hip)
      linarith
    have dR : ∀ i ∈ Ico p n, Real.log (ρ (i + 1)) - Real.log (ρ i) ≤ 0 := by
      intro i hi'
      have hip := Finset.mem_Ico.mp hi'
      have := Real.log_le_log (hρ (i + 1) (by omega)) (h2 i hip.1 hip.2)
      linarith
    obtain ⟨A1, A2⟩ := sum_sub_lo_mul_bounds_of_nonneg _ a _ lo hi dL haL
    obtain ⟨B1, B2⟩ := sum_sub_lo_mul_bounds_of_nonpos _ a _ lo hi dR haR
    rw [hL] at A2
    rw [hR] at B1
    have hLnn : 0 ≤ Real.log (ρ p) := hL ▸ Finset.sum_nonneg dL
    rw [abs_of_nonneg hLnn, abs_le]
    constructor <;> linarith
  · have dL : ∀ i ∈ range p, Real.log (ρ (i + 1)) - Real.log (ρ i) ≤ 0 := by
      intro i hi'
      have hip := Finset.mem_range.mp hi'
      have := Real.log_le_log (hρ (i + 1) (by omega)) (h1 i hip)
      linarith
    have dR : ∀ i ∈ Ico p n, 0 ≤ Real.log (ρ (i + 1)) - Real.log (ρ i) := by
      intro i hi'
      have hip := Finset.mem_Ico.mp hi'
      have := Real.log_le_log (hρ i (by omega)) (h2 i hip.1 hip.2)
      linarith
    obtain ⟨A1, A2⟩ := sum_sub_lo_mul_bounds_of_nonpos _ a _ lo hi dL haL
    obtain ⟨B1, B2⟩ := sum_sub_lo_mul_bounds_of_nonneg _ a _ lo hi dR haR
    rw [hL] at A1
    rw [hR] at B2
    have hLnp : Real.log (ρ p) ≤ 0 := hL ▸ Finset.sum_nonpos dL
    rw [abs_of_nonpos hLnp, abs_le]
    constructor <;> linarith

end ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
end

