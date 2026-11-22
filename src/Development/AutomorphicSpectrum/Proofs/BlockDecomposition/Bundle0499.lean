import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdStage

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two in

theorem equiv_of_iso_two {p q c r t N : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) (H : Iso (two e (pr x hx) (pr y hy)) (pr w hz)) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := H

open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in

theorem equiv_of_iso {q c N : ℕ} (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (w a).1 = N) (H : Iso (pr y hy) (pr w hz)) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) := H

theorem ind₂_prodIrr_empty {c q N : ℕ} (x : Fin 0 → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = 0) (hy : ∑ a, (y a).1 = N)
    (hz : ∑ a, (w a).1 = N) (e : 0 + N = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have A : Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr y hy)) :=
    GlobalTheory.ProdReorder.ind₂_unit_left k N 0 e _ (prodIrr y hy) (isSmooth_prodIrr y hy)
      (fun a => (x a).1) (fun a => (x a).2.rep.V) (fun a => (x a).rep) (stdBlocks (fun a => (x a).1) hx)
  have B : Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) :=
    equiv_of_iso y w hy hz (GlobalTheory.ProdFlatten.pr_congr hw.symm hy hz)
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem ind₂_prodIrr_equiv_zero {q c r t N : ℕ} (x : Fin 0 → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have hr : r = 0 := by simpa using hx.symm
  subst hr
  have ht : t = N := by omega
  subst ht
  exact ind₂_prodIrr_empty x y w hw hx hy hz e

theorem ind₂_prodIrr_equiv_pos {p q c r t N : ℕ} (hp : p ≠ 0) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k)
    (w : Fin c → IrrGL k) (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r)
    (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) :=
  equiv_of_iso_two x y w hx hy hz e
    (GlobalTheory.ProdFlatten.iso_symm (GlobalTheory.ProdFlatten.pr_append x y w hw (Or.inl hp) hx hy hz e))

theorem ind₂_prodIrr_equiv {p q c r t N : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  cases p with
  | zero => exact ind₂_prodIrr_equiv_zero x y w (by simpa using hw) hx hy hz e
  | succ n => exact ind₂_prodIrr_equiv_pos (Nat.succ_ne_zero n) x y w hw hx hy hz e

theorem prod₂_prodIrr_append : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k)
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t),
    Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)) :=
  fun _ _ _ _ _ _ _ _ _ x y hx hy h =>
    ind₂_prodIrr_equiv x y (Fin.append x y) (List.ofFn_fin_append x y) hx hy h rfl

end GlobalTheory.CompanionTheory.ProdStage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiPreservesIsomorphism
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.PsiIso

private theorem mapQ_eq_id_of_eq_id {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) {f : M →ₗ[R] M} (hf : f = LinearMap.id) (h : p ≤ p.comap f) :
    p.mapQ p f h = LinearMap.id := by
  subst hf
  exact Submodule.mapQ_id p h

private theorem mapQ_congr {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
    [Module R M₂] (p : Submodule R M) (q : Submodule R M₂) {f g : M →ₗ[R] M₂} (hfg : f = g)
    (hf : p ≤ q.comap f) (hg : p ≤ q.comap g) : p.mapQ q f hf = p.mapQ q g hg := by
  subst hfg
  rfl

theorem twAct_equiv {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  let eL : V ≃ₗ[ℂ] W :=
    { e.toIntertwiningMap.toLinearMap with
      invFun := e.invFun
      left_inv := e.left_inv
      right_inv := e.right_inv }
  have hf : ∀ (g : G) (v : V), (eL : V →ₗ[ℂ] W) (ρ g v) = σ g ((eL : V →ₗ[ℂ] W) v) :=
    fun g v => Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v
  have hg : ∀ (g : G) (w : W), (eL.symm : W →ₗ[ℂ] V) (σ g w) = ρ g ((eL.symm : W →ₗ[ℂ] V) w) := by
    intro g w
    apply eL.injective
    have := hf g (eL.symm w)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    exact this.symm
  have hf' : ∀ (g : G) (v : V), eL (ρ g v) = σ g (eL v) := hf
  have hfc : ∀ g : G, (eL : V →ₗ[ℂ] W) ∘ₗ ρ g = σ g ∘ₗ (eL : V →ₗ[ℂ] W) :=
    fun g => LinearMap.ext fun v => hf g v
  let F := GlobalTheory.BZMir.twMap ρ σ N θ (eL : V →ₗ[ℂ] W) hf
  let F' := GlobalTheory.BZMir.twMap σ ρ N θ (eL.symm : W →ₗ[ℂ] V) hg
  have hF'F : F' ∘ₗ F = LinearMap.id := by
    simp only [F, F', GlobalTheory.BZMir.twMap]
    rw [← Submodule.mapQ_comp]
    refine mapQ_eq_id_of_eq_id _ ?_ _
    ext v
    simp
  have hFF' : F ∘ₗ F' = LinearMap.id := by
    simp only [F, F', GlobalTheory.BZMir.twMap]
    rw [← Submodule.mapQ_comp]
    refine mapQ_eq_id_of_eq_id _ ?_ _
    ext w
    simp
  have hcomm : ∀ m : M, F ∘ₗ GlobalTheory.BZMir.twAct ρ N θ s hs m =
      GlobalTheory.BZMir.twAct σ N θ s hs m ∘ₗ F := by
    intro m
    first
      | (simp only [F, GlobalTheory.BZMir.twMap, GlobalTheory.BZMir.twAct,
            MonoidHom.coe_mk, OneHom.coe_mk]
         erw [← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
         exact mapQ_congr _ _ (hfc (s m)) _ _)
      | (apply Submodule.linearMap_qext
         ext v
         simp [F, GlobalTheory.BZMir.twMap, GlobalTheory.BZMir.twAct, hf, hf'])
  exact ⟨⟨⟨F, hcomm⟩, F', fun x => LinearMap.congr_fun hF'F x, fun y => LinearMap.congr_fun hFF' y⟩⟩

theorem giso_psiN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  intro k _ _ _ _ n A B ⟨e⟩
  exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw _
    (GlobalTheory.CompanionTheory.LeibOrd.PsiIso.twAct_equiv e (GlobalTheory.BZMir.MirUin k n) 1
      (GlobalTheory.BZMir.levi k n) (GlobalTheory.BZMir.levi_normalises n))

end GlobalTheory.CompanionTheory.LeibOrd.PsiIso

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem trace_norm_local_sizes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl F) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  intro F E _ _ _ _ _ σ hCM x
  obtain ⟨_, hEc, hfin2, hconj⟩ := hCM
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ z, σ (σ z) = z := fun z => τ0.injective (by rw [hconj, hconj, star_star])
  have hσne : ∃ w, σ w ≠ w := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ0 := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun w => ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have h1 := hconj τ0 w
      rw [hcon w] at h1
      exact h1.symm
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEc.isComplex (InfinitePlace.mk τ0)) ⟨τ0, hreal, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ z : E, σ z = z → ∃ y : F, algebraMap F E y = z := by
    intro z hz
    have hSle : Submodule.span F {(1 : E)} ≤ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      simp
    have hker : LinearMap.ker (σ.toLinearMap - LinearMap.id) ≠ ⊤ := by
      intro htop
      obtain ⟨w, hw⟩ := hσne
      have hw' : w ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hw'
      exact hw (sub_eq_zero.1 hw')
    have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
    have hlt := Submodule.finrank_lt hker
    have hge := Submodule.finrank_mono hSle
    have heq := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
    have hzk : z ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [LinearMap.mem_ker]
      simp [hz]
    rw [← heq] at hzk
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hzk
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨y₁, hy₁⟩ := hfix (x + σ x) (by rw [map_add, hσσ, add_comm])
  obtain ⟨y₂, hy₂⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
  refine ⟨y₁, y₂, by rw [hy₁, hy₂]; ring, fun v τ => ?_⟩
  have key : ∀ y : F, τ (algebraMap F E y) =
      algebraMap (Fv F v) (FvBar F v) (algebraMap F (Fv F v) y) := fun y => by
    rw [τ.commutes]
    exact IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v) y
  constructor
  · rw [← absBar_algebraMap F v, ← key, hy₁, map_add]
    exact absBar_add_le F v _ _
  · rw [← absBar_algebraMap F v, ← key, hy₂, map_mul]
    exact absBar_mul F v _ _

end GlobalTheory.CompanionTheory.GodementH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.SiegelDecay

theorem ratio_le_of_le {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (i j : Fin n) (hij : i ≤ j) :
    ρ j / ρ i ≤ max 1 t⁻¹ ^ n := by
  set S := max 1 t⁻¹
  have hS1 : 1 ≤ S := le_max_left _ _
  have hstep : ∀ l : ℕ, ∀ (hl : l + 1 < n), ρ ⟨l + 1, hl⟩ ≤ S * ρ ⟨l, by omega⟩ := by
    intro l hl
    have h := hs ⟨l, by omega⟩ ⟨l + 1, hl⟩ rfl
    have h2 : ρ ⟨l + 1, hl⟩ ≤ t⁻¹ * ρ ⟨l, by omega⟩ := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hρ _).le)
  have hchain : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < n),
      ρ ⟨a + d, ha⟩ ≤ S ^ d * ρ ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; simp
    | succ d ih =>
      intro a ha
      calc ρ ⟨a + (d + 1), ha⟩ ≤ S * ρ ⟨a + d, by omega⟩ := hstep (a + d) ha
        _ ≤ S * (S ^ d * ρ ⟨a, by omega⟩) :=
            mul_le_mul_of_nonneg_left (ih a (by omega)) (by linarith)
        _ = S ^ (d + 1) * ρ ⟨a, by omega⟩ := by ring
  have hij' : (i : ℕ) ≤ j := hij
  have h1 := hchain (j - i) i (by omega)
  have hj : (⟨(i : ℕ) + (j - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [hj] at h1
  rw [div_le_iff₀ (hρ _)]
  calc ρ j ≤ S ^ ((j : ℕ) - i) * ρ i := h1
    _ ≤ S ^ n * ρ i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS1 (by omega)) (hρ _).le

theorem ratio_le_all {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) {A : ℝ} (hA1 : 1 ≤ A)
    (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n) (i j : Fin n) :
    ρ i / ρ j ≤ max 1 t⁻¹ ^ n * A ^ n := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  rcases lt_or_ge i j with h | h
  · exact (hA i j h).trans (le_mul_of_one_le_left (by linarith) hT)
  · exact (ratio_le_of_le ht hρ hs j i h).trans (le_mul_of_one_le_right (by linarith) hAn)

theorem le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : ρ i ≤ R := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact i.elim0
  have h1 : ρ i ^ n = ∏ j, ρ i / ρ j := by
    rw [Finset.prod_div_distrib, hprod, div_one]
    simp
  have h2 : ρ i ^ n ≤ R ^ n := by
    rw [h1]
    calc ∏ j, ρ i / ρ j ≤ ∏ _j : Fin n, R :=
          Finset.prod_le_prod (fun j _ => (div_pos (hρ i) (hρ j)).le) (fun j _ => h i j)
      _ = R ^ n := by simp
  exact (pow_le_pow_iff_left₀ (hρ i).le (by linarith) hn).1 h2

theorem inv_le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : R⁻¹ ≤ ρ i := by
  have h1 : (ρ i)⁻¹ ≤ R := by
    refine le_of_ratio_le (ρ := fun i => (ρ i)⁻¹) (fun i => inv_pos.2 (hρ i)) ?_ hR ?_ i
    · rw [Finset.prod_inv_distrib, hprod, inv_one]
    · intro i j
      have := h j i
      rwa [inv_div_inv]
  exact inv_le_of_inv_le₀ (hρ i) h1

theorem one_le_rpow_mul_prod {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {R : ℝ} (hR : 1 ≤ R)
    (hb : ∀ i, ρ i ≤ R) (hb' : ∀ i, R⁻¹ ≤ ρ i) (lam : Fin n → ℝ) :
    1 ≤ R ^ (∑ i, |lam i|) * ∏ i, ρ i ^ lam i := by
  have hR0 : 0 < R := by linarith
  rw [Real.rpow_sum_of_pos hR0, ← Finset.prod_mul_distrib]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => ?_)
  rcases le_total 0 (lam i) with hl | hl
  · rw [abs_of_nonneg hl, ← Real.mul_rpow hR0.le (hρ i).le]
    refine Real.one_le_rpow ?_ hl
    have := mul_le_mul_of_nonneg_left (hb' i) hR0.le
    rwa [mul_inv_cancel₀ hR0.ne'] at this
  · have hρ' : ρ i ^ lam i = ((ρ i)⁻¹) ^ (-lam i) := by
      rw [Real.inv_rpow (hρ i).le, Real.rpow_neg (hρ i).le, inv_inv]
    rw [abs_of_nonpos hl, hρ', ← Real.mul_rpow hR0.le (inv_pos.2 (hρ i)).le]
    refine Real.one_le_rpow ?_ (by linarith)
    rw [← div_eq_mul_inv, one_le_div (hρ i)]
    exact hb i

theorem one_le_weight {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (hprod : ∏ i, ρ i = 1)
    {A : ℝ} (hA1 : 1 ≤ A) (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n)
    (lam : Fin n → ℝ) (M : ℕ) (hM : (n : ℝ) * ∑ i, |lam i| ≤ M) :
    1 ≤ (max 1 t⁻¹ ^ n) ^ (∑ i, |lam i|) * A ^ M * ∏ i, ρ i ^ lam i := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  have hA0 : 0 < A := by linarith
  have hR : 1 ≤ max 1 t⁻¹ ^ n * A ^ n := one_le_mul_of_one_le_of_one_le hT hAn
  have hrat := ratio_le_all ht hρ hs hA1 hA
  have h := one_le_rpow_mul_prod hρ hR (le_of_ratio_le hρ hprod hR hrat)
    (inv_le_of_ratio_le hρ hprod hR hrat) lam
  have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
  have hpow : (A ^ n) ^ (∑ i, |lam i|) ≤ A ^ M := by
    rw [← Real.rpow_natCast A n, ← Real.rpow_mul hA0.le, ← Real.rpow_natCast A M]
    exact Real.rpow_le_rpow_of_exponent_le hA1 hM
  rw [Real.mul_rpow (by linarith) (by linarith)] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hP)
  exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith) _)

theorem rapid_decay_of_one_parabolic_bounds : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), Continuous φ → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ (r : ℕ) (hr0 : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∏ i, ρ i = 1 → ∀ kk ∈ maxCompact (K := K) (n := n), ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, ρ i / ρ j ≤ R) →
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
            C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩) ^ k * R ^ N) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ lam : Fin n → ℝ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        ∏ i, r i = 1 → ∀ k ∈ maxCompact (K := K) (n := n),
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) * k)‖ ≤ C * ∏ i, r i ^ lam i) := by
  intro K _ _ n φ hφ hyp ω hω hωB hdet t ht lam
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain ⟨C, hC⟩ := (hω.mul (isCompact_maxCompact (K := K) (n := n))).exists_bound_of_continuousOn
      hφ.continuousOn
    refine ⟨C, fun b hb r hr hs hprod k hk => ?_⟩
    have hr1 : ∀ i, r i = 1 := by
      intro i
      have h1 : n = 1 := by
        have := i.pos
        omega
      subst h1
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hprod
    have hd : diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
      have h1 : (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
        funext i
        have h2 : (⟨r i, hr i⟩ : {x : ℝ // 0 < x}) = 1 := Subtype.ext (hr1 i)
        change posIdeleHom K ⟨r i, hr i⟩ = 1
        rw [h2, map_one]
      rw [h1, map_one]
    have hP : ∏ i, r i ^ lam i = 1 :=
      Finset.prod_eq_one fun i _ => by rw [hr1 i, Real.one_rpow]
    rw [hd, hP, mul_one, mul_one]
    exact hC _ (Set.mul_mem_mul hb hk)
  · set T : ℝ := max 1 t⁻¹ ^ n with hTdef
    have hT1 : 1 ≤ T := one_le_pow₀ (le_max_left _ _)
    have hT0 : 0 < T := by linarith
    set L : ℝ := ∑ i, |lam i| with hL
    obtain ⟨M, hM⟩ := exists_nat_ge ((n : ℝ) * L)
    have key : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ D : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ)
        (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → ∏ i, ρ i = 1 →
        ∀ kk ∈ maxCompact (K := K) (n := n),
        (∀ i j : Fin n, i < j → ρ i / ρ j ≤ max 1 (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩) ^ n) →
        ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
          max D 0 * ∏ i, ρ i ^ lam i := by
      intro r hr hrn
      obtain ⟨N, hN⟩ := hyp ω hω hωB hdet t ht r hr hrn
      obtain ⟨C0, hC0⟩ := hN 0
      obtain ⟨C1, hC1⟩ := hN (n * N + M)
      set E : ℝ := max C0 0 + max C1 0 with hE
      have hE0 : 0 ≤ E := add_nonneg (le_max_right _ _) (le_max_right _ _)
      have hC0E : C0 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
      have hC1E : C1 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
      have hTL : 0 < T ^ L := Real.rpow_pos_of_pos hT0 _
      have hD0 : 0 ≤ E * T ^ N * T ^ L := by positivity
      refine ⟨E * T ^ N * T ^ L, ?_⟩
      rw [max_eq_left hD0]
      intro b hb ρ hρ hs hprod kk hkk hmax
      have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩ =
          (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩)⁻¹ := by rw [inv_div]
      obtain ⟨α, hα⟩ : ∃ α, α = ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ := ⟨_, rfl⟩
      rw [← hα] at hmax hgain
      have hα0 : 0 < α := by rw [hα]; exact div_pos (hρ _) (hρ _)
      set P : ℝ := ∏ i, ρ i ^ lam i with hPdef
      have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
      rcases le_or_gt α 1 with hα1 | hα1
      · rw [max_eq_left hα1] at hmax
        have hone := one_le_weight ht hρ hs hprod le_rfl hmax lam M hM
        rw [one_pow, mul_one] at hone
        have h := hC0 b hb ρ hρ hs hprod kk hkk T hT1 fun i j => by
          simpa using ratio_le_all ht hρ hs le_rfl hmax i j
        rw [pow_zero, mul_one] at h
        calc _ ≤ C0 * T ^ N := h
          _ ≤ E * T ^ N := mul_le_mul_of_nonneg_right hC0E (by positivity)
          _ ≤ E * T ^ N * (T ^ L * P) := le_mul_of_one_le_right (by positivity) hone
          _ = E * T ^ N * T ^ L * P := by ring
      · rw [max_eq_right hα1.le] at hmax
        have hone := one_le_weight ht hρ hs hprod hα1.le hmax lam M hM
        have hαn : 1 ≤ α ^ n := one_le_pow₀ hα1.le
        have h := hC1 b hb ρ hρ hs hprod kk hkk (T * α ^ n)
          (one_le_mul_of_one_le_of_one_le hT1 hαn) (ratio_le_all ht hρ hs hα1.le hmax)
        rw [hgain] at h
        have hpow : (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N = T ^ N * (α ^ M)⁻¹ := by
          have ha : α ^ (n * N) ≠ 0 := (pow_pos hα0 _).ne'
          rw [mul_pow, ← pow_mul α n N, inv_pow, pow_add, mul_inv]
          calc (α ^ (n * N))⁻¹ * (α ^ M)⁻¹ * (T ^ N * α ^ (n * N))
              = ((α ^ (n * N))⁻¹ * α ^ (n * N)) * (T ^ N * (α ^ M)⁻¹) := by ring
            _ = T ^ N * (α ^ M)⁻¹ := by rw [inv_mul_cancel₀ ha, one_mul]
        have hX : 0 ≤ T ^ N * (α ^ M)⁻¹ := by positivity
        calc _ ≤ C1 * (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N := h
          _ = C1 * (T ^ N * (α ^ M)⁻¹) := by rw [mul_assoc, hpow]
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) := mul_le_mul_of_nonneg_right hC1E hX
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) * (T ^ L * α ^ M * P) :=
              le_mul_of_one_le_right (mul_nonneg hE0 hX) hone
          _ = E * T ^ N * T ^ L * P := by
              have : α ^ M ≠ 0 := (pow_pos hα0 _).ne'
              field_simp
    choose D hD using key
    refine ⟨∑ r : Fin n, if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0, ?_⟩
    intro b hb ρ hρ hs hprod k hk
    obtain ⟨r, hr, hrn, hratio⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_le_max_pow hn ρ hρ
    have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
    refine (hD r hr hrn b hb ρ hρ hs hprod k hk hratio).trans
      (mul_le_mul_of_nonneg_right ?_ hP)
    have h1 := Finset.single_le_sum (f := fun r : Fin n =>
      if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hrn⟩)
    simpa only [hr, dif_pos] using h1

end GlobalTheory.CompanionTheory.SiegelDecay
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLe
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem relIndex_open_compact_and_twisted :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H),
      IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧
        ∀ (T C : Subgroup H) (x : H),
          (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 →
            (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  intro H _ _ _ K L hL hK hLK
  have hKL : L.relIndex K ≠ 0 := by
    haveI := isCompact_iff_compactSpace.mp hK
    haveI : Finite (K ⧸ L.subgroupOf K) :=
      Subgroup.quotient_finite_of_isOpen _ (hL.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨hKL, fun T C x hC => ?_⟩
  have hf : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have h1 : (L.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rwa [Subgroup.relIndex_map_map_of_injective L K hf]
  have h2 : (L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 :=
    fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h)
  have h3 : T.relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rw [Subgroup.relIndex_eq_one.mpr inf_le_left]
    exact one_ne_zero
  exact Subgroup.relIndex_ne_zero_trans (Subgroup.relIndex_inf_ne_zero h3 h2) hC

end GlobalTheory.CompanionTheory.OrbitalCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationRealStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_classification_real : PositivityTheory.RgBcC.RealD.SemiCls := by
  first | exact @GlobalTheory.CompanionTheory.SemiClass.semiCls | exact GlobalTheory.CompanionTheory.SemiClass.semiCls | (intros; apply GlobalTheory.CompanionTheory.SemiClass.semiCls <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMemStatement
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_conjugate_inverse_mem : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ {φ : GA E a → ℂ}, φ ∈ Sm E a → (fun g => star (φ (invA E a g))) ∈ Sm E a := by
  first | exact @GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | exact GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | (intros; apply GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm <;> assumption)
end

