import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_heisenberg_relations_one_variable : ∀ d : ℕ, 0 < d → (∀ (x y : ℂ) (F : ℂ → ℂ), U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) * U1 d (x + y) F z) ∧ (∀ F, U1 d 0 F = F) ∧ (∀ (x : ℂ) (F : ℂ → ℂ), Differentiable ℂ F → Differentiable ℂ (U1 d x F) ∧ Differentiable ℂ (W1 d x F)) ∧ (∀ (x : ℂ) (F : ℂ → ℂ) (z : ℂ), U1 d x (fun z => F (-z)) z = U1 d (-x) F (-z)) ∧ (∀ (x y : ℂ) (F : ℂ → ℂ), d % 4 = 3 → InOK d (x * conj y) → W1 d x (W1 d y F) = W1 d (x + y) F) ∧ (∀ (θ : ℂ → ℂ) (t l z : ℂ), W1 d l θ = θ → U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l))) ∧ (∀ (x : ℂ) (f F : ℂ → ℂ) (z : ℂ), W1 d x (fun z => f z * F z) z = f (z + x) * W1 d x F z ∧ U1 d x (fun z => f z * F z) z = f (z + x) * U1 d x F z) ∧ ∀ (x y z : ℂ), kap1 d x (y + z) = kap1 d x y * kap1 d x z ∧ kap1 d (x + y) z = kap1 d x z * kap1 d y z := by
  first | exact @GlobalTheory.MomOne.heisenbergOne | exact GlobalTheory.MomOne.heisenbergOne | (intros; apply GlobalTheory.MomOne.heisenbergOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffProdLeadingMinors
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.LeadingMinors

open MvPowerSeries in

theorem _root_.GlobalTheory.LeadingMinors.isHomogeneous_det_X {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det.IsHomogeneous
      (Fintype.card ι) := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)) (e i) i)
    (fun _ => 1) fun i _ => MvPolynomial.isHomogeneous_X k _
  simpa using h

open MvPowerSeries in

theorem _root_.GlobalTheory.LeadingMinors.det_X_mem_supported {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) (S : Set σ) (hS : ∀ a i, v a i ∈ S) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det ∈
      MvPolynomial.supported k S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun e _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (Subalgebra.prod_mem _ fun i _ => ?_) _
  exact Algebra.subset_adjoin (Set.mem_image_of_mem MvPolynomial.X (hS (e i) i))

open MvPowerSeries in

theorem _root_.GlobalTheory.LeadingMinors.killCompl_det_X {k σ ρ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] {f : ρ → σ} (hf : Function.Injective f) (v : ι → ι → σ) (u : ι → ρ)
    (hd : ∀ a, v a a = f (u a)) (ho : ∀ a i, a ≠ i → v a i ∉ Set.range f) :
    MvPolynomial.killCompl hf
      (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det =
      MvPolynomial.monomial (∑ a, Finsupp.single (u a) 1) 1 := by
  rw [AlgHom.map_det]
  have hM : (MvPolynomial.killCompl hf).mapMatrix
      (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)) =
      Matrix.diagonal fun a => MvPolynomial.X (u a) := by
    ext a i
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rw [hd, ← MvPolynomial.rename_X f, MvPolynomial.killCompl_rename_app]
    · rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg (ho a i h)]
  rw [hM, Matrix.det_diagonal, MvPolynomial.monomial_sum_one]
  rfl

open MvPowerSeries in

theorem _root_.GlobalTheory.LeadingMinors.coeff_prod_leading_minors : ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → P.coeff al = 1 ∧ P.IsHomogeneous al.degree ∧ al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) ∧ ∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → ∃ i, col l.1 i = b := by
  intro k _ T _ _ r n col m hcol P al hP hal
  have hf : Function.Injective
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) :=
    fun a b h => congrArg Prod.fst h
  have hblock : ∀ τ (s : Fin (r τ)), MvPolynomial.killCompl hf
      (Matrix.of fun a i : Fin (s.val + 1) =>
        (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det =
      MvPolynomial.monomial
        (∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1)
        1 := fun τ s =>
    _root_.GlobalTheory.LeadingMinors.killCompl_det_X hf _ (fun a => ⟨τ, Fin.castLE s.isLt a⟩)
      (fun _ => rfl) (by
        rintro a i hai ⟨l, hl⟩
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, h⟩ := hl
        exact hai (Fin.castLE_injective _ (hcol τ h)))
  set B : (Σ τ : T, Fin (r τ)) →₀ ℕ := ∑ τ, ∑ s : Fin (r τ), m τ s •
    ∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1
    with hBdef
  have hkill : MvPolynomial.killCompl hf P = MvPolynomial.monomial B 1 := by
    rw [hP, hBdef, map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, hblock, MvPolynomial.monomial_pow, one_pow]
  have hmap : Finsupp.mapDomain
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) B = al := by
    rw [hal, hBdef]
    simp [Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  have hdeg : al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) := by
    rw [hal]
    simp [map_sum, Finsupp.degree_single]
  have hhom : P.IsHomogeneous (∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1)) := by
    rw [hP]
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ fun s _ => ?_
    have h := (_root_.GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := k)
      (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
        col τ (Fin.castLE s.isLt i)))).pow (m τ s)
    rw [Fintype.card_fin] at h
    rwa [mul_comm] at h
  have hsupp : P ∈ MvPolynomial.supported k
      {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2} := by
    rw [hP]
    exact Subalgebra.prod_mem _ fun τ _ => Subalgebra.prod_mem _ fun s _ =>
      Subalgebra.pow_mem _ (_root_.GlobalTheory.LeadingMinors.det_X_mem_supported
        (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)))
        {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2}
        fun a i => ⟨Fin.castLE s.isLt i, rfl⟩) _
  refine ⟨?_, by rw [hdeg]; exact hhom, hdeg, fun mo hmo l b hlb => ?_⟩
  · rw [← hmap, ← MvPolynomial.coeff_killCompl hf, hkill, MvPolynomial.coeff_monomial, if_pos rfl]
  · have hv : (l, b) ∈ P.vars :=
      (MvPolynomial.mem_vars _).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hlb⟩
    exact MvPolynomial.mem_supported.1 hsupp hv

end GlobalTheory.LeadingMinors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ColValueMulOfDisjointColumns
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem sum_coeff_mul_weight {k σ : Type} [CommRing k] (w : (σ →₀ ℕ) → k) (P₁ P₂ : MvPolynomial σ k) :
    ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * w mo =
      ∑ m₁ ∈ P₁.support, ∑ m₂ ∈ P₂.support, P₁.coeff m₁ * P₂.coeff m₂ * w (m₁ + m₂) := by
  let L : MvPolynomial σ k →ₗ[k] k := (MvPolynomial.basisMonomials σ k).constr k w
  have hL : ∀ (m : σ →₀ ℕ) (a : k), L (MvPolynomial.monomial m a) = a * w m := by
    intro m a
    have h1 : (MvPolynomial.monomial m a : MvPolynomial σ k) =
        a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.coe_basisMonomials]
      simp [MvPolynomial.smul_monomial]
    rw [h1, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hP : ∀ P : MvPolynomial σ k, L P = ∑ mo ∈ P.support, P.coeff mo * w mo := by
    intro P
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hL m _
  rw [← hP]
  conv_lhs => rw [P₁.as_sum, P₂.as_sum]
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [MvPolynomial.monomial_mul, hL]

theorem colValue_mul_of_disjoint_columns :
    ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (n : ℕ) (mu : Fin n → (ι →₀ ℕ) → k) (T : Finset (Fin n)) (P₁ P₂ : MvPolynomial (ι × Fin n) k), (∀ mo ∈ P₁.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ T) → (∀ mo ∈ P₂.support, ∀ l b, mo (l, b) ≠ 0 → b ∉ T) → ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * ∏ b, mu b (colM mo b) = (∑ mo ∈ P₁.support, P₁.coeff mo * ∏ b ∈ T, mu b (colM mo b)) * ∑ mo ∈ P₂.support, P₂.coeff mo * ∏ b ∈ Tᶜ, mu b (colM mo b) := by
  intro k _ ι _ n mu T P₁ P₂ h₁ h₂
  rw [sum_coeff_mul_weight (fun mo => ∏ b, mu b (colM mo b)) P₁ P₂, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
  have e₁ : ∏ b ∈ T, mu b (colM (m₁ + m₂) b) = ∏ b ∈ T, mu b (colM m₁ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₂ (l, b) = 0 := by
      by_contra h
      exact h₂ m₂ hm₂ l b h hb
    simp [colM, this]
  have e₂ : ∏ b ∈ Tᶜ, mu b (colM (m₁ + m₂) b) = ∏ b ∈ Tᶜ, mu b (colM m₂ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₁ (l, b) = 0 := by
      by_contra h
      exact (Finset.mem_compl.1 hb) (h₁ m₁ hm₁ l b h)
    simp [colM, this]
  rw [← Finset.prod_mul_prod_compl T, e₁, e₂]
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfCongrJet
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.JetOnly

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_Dof_congr (F : Fin d → PS k 2 d) (v : Fin d → k) (n : ℕ) (f g : PS k 1 d)
    (h : ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + 1 → coeff mo f = coeff mo g)
    (mo : Fin 1 × Fin d →₀ ℕ) (hmo : mo.degree ≤ n) :
    coeff mo (Dof F v f) = coeff mo (Dof F v g) := by
  classical
  unfold Dof
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add]
  rw [coeff_pderiv, coeff_pderiv, h]
  rw [map_add, Finsupp.degree_single]
  omega

theorem coeff_iterate_Dof_congr (F : Fin d → PS k 2 d) (v : Fin d → k) (r : ℕ) :
    ∀ (n : ℕ) (f g : PS k 1 d),
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n →
        coeff mo ((Dof F v)^[r] f) = coeff mo ((Dof F v)^[r] g) := by
  induction r with
  | zero => intro n f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro n f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih n _ _ (coeff_Dof_congr F v (n + r) f g h) mo hmo

theorem coeff_foldr_Dof_congr (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k) (m : ι → ℕ)
    (f g : PS k 1 d) (L : List ι) :
    ∀ n : ℕ,
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n →
        coeff mo (L.foldr (fun l s => (Dof F (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (Dof F (u l))^[m l] s) g) := by
  induction L with
  | nil => intro n h mo hmo; exact h mo hmo
  | cons l L ih =>
    intro n h mo hmo
    rw [List.foldr_cons, List.foldr_cons]
    refine coeff_iterate_Dof_congr F (u l) (m l) n _ _ (ih (n + m l) fun mo' h' => h mo' ?_) mo hmo
    rw [List.map_cons, List.sum_cons]
    omega

theorem coeff_DmonOf_congr (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (m : ι →₀ ℕ) (f g : PS k 1 d) (n : ℕ)
    (h : ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + m.degree → coeff mo f = coeff mo g)
    (mo : Fin 1 × Fin d →₀ ℕ) (hmo : mo.degree ≤ n) :
    coeff mo (DmonOf F u m f) = coeff mo (DmonOf F u m g) := by
  unfold DmonOf
  refine coeff_foldr_Dof_congr F u m f g _ n (fun mo' h' => h mo' ?_) mo hmo
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum] at h'

end GlobalTheory.JetOnly

namespace GlobalTheory

theorem constantCoeff_DmonOf_congr_jet :
    ∀ (k : Type) [CommRing k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
      (u : ι → Fin d → k) (m : ι →₀ ℕ) (f g : PS k 1 d),
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) →
      constantCoeff (DmonOf F u m f) = constantCoeff (DmonOf F u m g) := by
  intro k _ d F ι _ u m f g h
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  exact JetOnly.coeff_DmonOf_congr F u m f g 0 (fun mo h' => h mo (by simpa using h')) 0 (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfSubMem
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.EigenCongruence

variable {R : Type} [CommRing R] {d : ℕ}

def coeffIdeal {σ : Type} (I : Ideal R) : Ideal (MvPowerSeries σ R) where
  carrier := {g | ∀ mo, coeff mo g ∈ I}
  add_mem' := by
    intro a b ha hb mo
    rw [map_add]
    exact I.add_mem (ha mo) (hb mo)
  zero_mem' := by
    intro mo
    rw [map_zero]
    exact I.zero_mem
  smul_mem' := by
    classical
    intro c x hx mo
    rw [smul_eq_mul, coeff_mul]
    exact I.sum_mem fun p _ => I.mul_mem_left _ (hx p.2)

theorem mem_coeffIdeal {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R} :
    g ∈ coeffIdeal I ↔ ∀ mo, coeff mo g ∈ I := Iff.rfl

theorem pderiv_mem_coeffIdeal {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R}
    (hg : g ∈ coeffIdeal I) (s : σ) : pderiv R s g ∈ coeffIdeal I := by
  intro mo
  rw [coeff_pderiv]
  exact I.mul_mem_right _ (hg _)

theorem dof_mem_coeffIdeal (F : Fin d → PS R 2 d) (v : Fin d → R) {I : Ideal R} {g : PS R 1 d}
    (hg : g ∈ coeffIdeal I) : Dof F v g ∈ coeffIdeal I :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (pderiv_mem_coeffIdeal hg _)

theorem dof_step (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R} {f g : PS R 1 d}
    (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I) :
    Dof F v g - C (y * c) * f ∈ coeffIdeal I := by
  have h1 : Dof F v g = Dof F v (g - C c * f) + C c * Dof F v f := by
    rw [← GE.dof_C_mul, ← GE.dof_add, sub_add_cancel]
  have h2 : Dof F v g - C (y * c) * f =
      Dof F v (g - C c * f) + C c * (Dof F v f - C y * f) := by
    rw [h1, map_mul]; ring
  rw [h2]
  exact Ideal.add_mem _ (dof_mem_coeffIdeal F v hg) (Ideal.mul_mem_left _ _ hf)

theorem dof_iterate (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R}
    {f g : PS R 1 d} (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I)
    (n : ℕ) : (Dof F v)^[n] g - C (y ^ n * c) * f ∈ coeffIdeal I := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact dof_step F v y _ hf ih

theorem foldr_sub_mem (F : Fin d → PS R 2 d) {I : Ideal R} {ι : Type} (u : ι → Fin d → R)
    (y : ι → R) (f : PS R 1 d) (hf : ∀ l, Dof F (u l) f - C (y l) * f ∈ coeffIdeal I)
    (m : ι → ℕ) (L : List ι) :
    L.foldr (fun l g => (Dof F (u l))^[m l] g) f - C (L.map fun l => y l ^ m l).prod * f ∈
      coeffIdeal I := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    exact dof_iterate F (u a) (y a) _ (hf a) ih (m a)

theorem dmonOf_sub_mem (F : Fin d → PS R 2 d) {I : Ideal R} {ι : Type} [Fintype ι]
    (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d)
    (hf : ∀ l, Dof F (u l) f - C (y l) * f ∈ coeffIdeal I) (m : ι →₀ ℕ) :
    DmonOf F u m f - C (∏ l, y l ^ m l) * f ∈ coeffIdeal I := by
  have h := foldr_sub_mem F u y f hf m (Finset.univ : Finset ι).toList
  rwa [Finset.prod_map_toList] at h

end GlobalTheory.EigenCongruence

namespace GlobalTheory

theorem constantCoeff_dmonOf_sub_mem :
    ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι]
      (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d),
      (∀ l mo, coeff mo (Dof F (u l) f - C (y l) * f) ∈ I) →
      ∀ m : ι →₀ ℕ, constantCoeff (DmonOf F u m f) - (∏ l, y l ^ m l) * constantCoeff f ∈ I := by
  intro R _ d F I ι _ u y f hf m
  have h := EigenCongruence.dmonOf_sub_mem F u y f hf m 0
  rwa [coeff_zero_eq_constantCoeff, map_sub, map_mul, constantCoeff_C] at h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositioStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log : ∀ (q : ℕ) [Fact q.Prime], (∀ a : ℤ_[q], Bd 1 (mulS a : ℂ_[q]⟦X⟧) ∧ constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 ∧ coeff 1 (mulS a : ℂ_[q]⟦X⟧) = zc a ∧ (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS) ∧ (∀ a b : ℤ_[q], (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b)) ∧ (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X ∧ (∀ (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ), ‖a‖ = 1 → (Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f)) ∧ DT (logS : ℂ_[q]⟦X⟧) = 1 ∧ (∀ a : ℤ_[q], ‖zc a‖ = ‖a‖) := by
  first | exact @GlobalTheory.MomOne.MulSeries.mulS_laws | exact GlobalTheory.MomOne.MulSeries.mulS_laws | (intros; apply GlobalTheory.MomOne.MulSeries.mulS_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLawsStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧), constantCoeff ℓ = 0 → (∀ F G : ℂ → ℂ, AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 → hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G ∧ hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G ∧ ((∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) → hat ι ℓ F = hat ι ℓ G) ∧ (coeff 1 ℓ ≠ 0 → hat ι ℓ F = hat ι ℓ G → F =ᶠ[𝓝 0] G)) ∧ (∀ c : ℂ, hat ι ℓ (fun _ => c) = C (ι c)) ∧ hat ι ℓ (fun z => z) = ℓ ∧ (∀ F : ℂ → ℂ, constantCoeff (hat ι ℓ F) = ι (F 0)) ∧ (∀ F : ℂ → ℂ, AnalyticAt ℂ F 0 → derivative ℂ_[q] (hat ι ℓ F) = derivative ℂ_[q] ℓ * hat ι ℓ (deriv F)) ∧ (∀ (F : ℂ → ℂ) (α : ℂ), AnalyticAt ℂ F 0 → hat ι ℓ (fun z => F (α * z)) = hat ι (C (ι α) * ℓ) F) ∧ ∀ (F : ℂ → ℂ) (h : ℂ_[q]⟦X⟧), constantCoeff h = 0 → (hat ι ℓ F).subst h = hat ι (ℓ.subst h) F := by
  first | exact @GlobalTheory.MomOne.TaylorRead.hat_laws | exact GlobalTheory.MomOne.TaylorRead.hat_laws | (intros; apply GlobalTheory.MomOne.TaylorRead.hat_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXy
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.EllipticModel

theorem exists_mul_prod_eq_xy (q : ℕ) [Fact q.Prime] (M : Mdl q) (φ : ℂ → ℂ) (hM : M.Ok) (hφ : Ell M.L φ) :
    ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ),
      (∀ i, P i ∉ M.L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧
      ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀,
        φ z * (∏ i, (Polynomial.X - Polynomial.C (M.x (P i)))).eval (M.x z) =
          A.eval (M.x z) + B.eval (M.x z) * M.y z := by
  obtain ⟨m, P, A, B, hP, h⟩ := GlobalTheory.EllipticPoles.exists_mul_prod_eq M.L φ hφ
  have hc : M.c ≠ 0 := hM.1
  set r : ℂ := M.ι.symm (M.W.b₂ / 12) with hr
  set a₁ : ℂ := M.ι.symm M.W.a₁ with ha₁
  set a₃ : ℂ := M.ι.symm M.W.a₃ with ha₃
  have hx : ∀ z, M.L.weierstrassP z = M.c ^ 2 * (M.x z + r) := by
    intro z
    simp only [Mdl.x, ← hr]
    field_simp
    ring
  have hy : ∀ z, M.L.derivWeierstrassP z = M.c ^ 3 * (2 * M.y z + a₁ * M.x z + a₃) := by
    intro z
    simp only [Mdl.y, ← ha₁, ← ha₃]
    field_simp
    ring
  let g : Polynomial ℂ := Polynomial.C (M.c ^ 2) * (Polynomial.X + Polynomial.C r)
  let k : ℂ := ((M.c ^ 2) ^ m)⁻¹
  refine ⟨m, P,
    Polynomial.C k * (A.comp g + B.comp g * Polynomial.C (M.c ^ 3) *
      (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃)),
    Polynomial.C k * (B.comp g * Polynomial.C (2 * M.c ^ 3)), hP, fun z₀ => ?_⟩
  filter_upwards [h z₀] with z hz
  have hg : g.eval (M.x z) = M.L.weierstrassP z := by
    rw [hx z]; simp [g]
  have hprod : ∏ i, (M.L.weierstrassP z - M.L.weierstrassP (P i)) =
      (M.c ^ 2) ^ m * ∏ i, (M.x z - M.x (P i)) := by
    have : ∀ i, M.L.weierstrassP z - M.L.weierstrassP (P i) = M.c ^ 2 * (M.x z - M.x (P i)) := by
      intro i; rw [hx z, hx (P i)]; ring
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hk : k * (M.c ^ 2) ^ m = 1 := inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc))
  rw [hprod, hy z] at hz
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp, hg]
  linear_combination k * hz - (φ z * ∏ i, (M.x z - M.x (P i))) * hk

end GlobalTheory.EllipticModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEqStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_const_mul_of_forall_exists_norm_eq' : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι] (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ), DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) → ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  first | exact @GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq | exact GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq | (intros; apply GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoordsStatement
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperators_orthogonalFrame_coords : ∀ (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), 0 < S.d → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i) → (∀ v : Fin g → ℂ, v = ∑ i, (beta S.d S.Hm v (x i) / (a i : ℂ)) • x i) ∧ (∀ z w : Fin g → ℂ, hf S.Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 S.d (z i) (w i)) ∧ (∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ), (∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) → ∀ t z : Fin g → ℂ, opU S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 S.d (t i) (f j i) (z i) ^ a i ∧ opW S.d S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 S.d (t i) (f j i) (z i) ^ a i) ∧ ∀ (G : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ G → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys := by
  first | exact @GlobalTheory.MomOne.Frame.coord | exact GlobalTheory.MomOne.Frame.coord | (intros; apply GlobalTheory.MomOne.Frame.coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrimeStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → (InOK d 1 ∧ InOK d (wK d) ∧ ∀ α β, InOK d α → InOK d β → InOK d (α + β) ∧ InOK d (α * β) ∧ InOK d (-α) ∧ InOK d (conj α)) ∧ (∀ α, InOK d α → (∃ a : ℤ_[q], ι α = zc a) ∧ (∃ N : ℕ, (N : ℂ) = α * conj α) ∧ α ∈ algebraicClosure ℚ ℂ) ∧ (∀ (α : ℂ) (n : ℕ), InOK d α → ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ‖ι (conj α)‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α / (q : ℂ) ^ n)) ∧ (∀ m s : ℕ, Nat.Coprime s q → ∃ e, InOK d e ∧ ‖ι ((s : ℂ) * e) - 1‖ ≤ (q : ℝ) ^ (-(m : ℤ)) ∧ ‖ι (conj e)‖ ≤ (q : ℝ) ^ (-(m : ℤ))) ∧ (∀ n : ℕ, ∃ α, InOK d α ∧ ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ∧ ¬ InOK d (α / 2)) ∧ (∀ x y, InOK d x → InOK d y → ∃ k : ℤ, (h1 d x y).im = k) ∧ ¬ q ∣ d := by
  first | exact @GlobalTheory.MomOne.okArith | exact GlobalTheory.MomOne.okArith | (intros; apply GlobalTheory.MomOne.okArith <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqRaisingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l + 1) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wP L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wP | exact GlobalTheory.WigSh.inv_sq_le_wP | (intros; apply GlobalTheory.WigSh.inv_sq_le_wP <;> assumption)
end

