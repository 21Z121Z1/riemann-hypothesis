import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMult

section Rep

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realEquiv (c : H' ≃ₗᵢ⋆[ℂ] H) : H' ≃L[ℝ] H where
  toFun := c
  invFun := c.symm
  map_add' := map_add c
  map_smul' r x := by
    rw [← Complex.coe_smul, map_smulₛₗ]
    simp
  left_inv := c.symm_apply_apply
  right_inv := c.apply_symm_apply
  continuous_toFun := c.continuous
  continuous_invFun := c.symm.continuous

theorem expProd_mem (hJ : IsUnit J.det) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i, (Xs i)ᴴ * J + J * Xs i = 0) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH J := by
  refine List.prod_induction _ (fun a b => mul_mem_UH J) (one_mem_UH J) fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact GlobalTheory.SmoothAutCheck.exp_mem_UH hJ (hX i) _

theorem smoothVec_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ' w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (c w) := by
  intro k Xs hX
  have := (realEquiv c).contDiff.comp (hw k Xs hX)
  convert this using 2 with t
  exact (hc _ (expProd_mem hJ hX t) w).symm

theorem span_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ' w}) :
    c w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ w} := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (smoothVec_conj hJ c hc hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem dRep_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * J + J * X = 0) (w : H') : dRep σ X (c w) = c (dRep σ' X w) := by
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (c w)) =
      realEquiv c ∘ fun t : ℝ => σ' (NormedSpace.exp (t • X)) w :=
    funext fun t => (hc _ (GlobalTheory.SmoothAutCheck.exp_mem_UH hJ hX t) w).symm
  rw [dRep, e, deriv, ContinuousLinearEquiv.comp_fderiv]
  rfl

theorem sobCont_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {ℓ : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ {X | Xᴴ * J + J * X = 0} σ ℓ) :
    ∃ ℓ' : H' →ₗ[ℂ] ℂ, Sobolev₂ {X | Xᴴ * J + J * X = 0} σ' ℓ' ∧ ∀ w, ℓ' w = star (ℓ (c w)) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨{ toFun := fun w => star (ℓ (c w))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }, ⟨S, C, hS, fun w hw => ?_⟩, fun _ => rfl⟩
  have e : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, Xᴴ * J + J * X = 0) →
      l.foldr (dRep σ) (c w) = c (l.foldr (dRep σ') w) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons X l ih =>
      intro hl
      rw [List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY), dRep_conj hJ c hc (hl X List.mem_cons_self),
        List.foldr_cons]
  have h1 := hC _ (smoothVec_conj hJ c hc hw)
  have h2 : (S.map fun l => ‖l.foldr (dRep σ) (c w)‖) = S.map fun l => ‖l.foldr (dRep σ') w‖ :=
    List.map_congr_left fun l hl => by rw [e l (hS l hl), c.norm_map]
  rw [h2] at h1
  exact (norm_star _).trans_le h1

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g.det) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    l.prod * g = g * (l.map fun a => g⁻¹ * a * g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, ih]
    simp only [mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hg]

theorem smoothVec_act (hJ : IsUnit J.det)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ g' ∈ Formalism.QuantumDeterminants.UH J, ∀ w, σ (g * g') w = σ g (σ g' w))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (σ g w) := by
  intro k Xs hX
  have hu := isUnit_of_UH hJ hg
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hi : (g⁻¹)ᴴ * J * g⁻¹ = J := by
    have : (hu.unit⁻¹).1 ∈ Formalism.QuantumDeterminants.UH J := (UG J).inv_mem (x := hu.unit) hg
    rwa [Matrix.coe_units_inv] at this
  have hg' : gᴴ * J * g = J := hg
  have hX' : ∀ i, (g⁻¹ * Xs i * g)ᴴ * J + J * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have h1 : (g⁻¹)ᴴ * J = J * g := by
      conv_rhs => rw [← hi]
      rw [Matrix.nonsing_inv_mul_cancel_right _ _ hd]
    have h2 : J * g⁻¹ = gᴴ * J := by
      conv_lhs => rw [← hg']
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    have h3 : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    calc _ = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * J) + J * g⁻¹ * Xs i * g := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * J + J * Xs i) * g := by rw [h1, h2]; simp only [mul_add, add_mul, mul_assoc]
      _ = 0 := by rw [h3, mul_zero, zero_mul]
  have := ((σ g).restrictScalars ℝ).contDiff.comp (hw k _ hX')
  convert this using 2 with t
  change _ = σ g (σ _ w)
  rw [← hm _ (expProd_mem hJ hX t) _ hg, ← hm _ hg _ (expProd_mem hJ hX' t), prod_conj hd, List.map_ofFn]
  congr 5
  funext i
  rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hu, mul_smul_comm, smul_mul_assoc]

end Rep

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := fun g hg => by
    have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    rw [← M.fr_gram τ] at hg'
    change _ * _ * _ = _
    calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  intro g hg g' hg' w
  have h := (M.ds τ).2.2.1.1.2 _ (key g hg) _ (key g' hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span (smoothVec_act (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (rep_mul M τ) hg hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem value_mem_homFun {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (h : IsMultMap θ M J χ T) (v : M.Vec) : T v ∈ homFun θ V := by
  classical
  have h1 : ∀ y ∈ realMon θ V, ∀ v, ∃ v', ∀ x, T v (x * y) = T v' x := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨τ, g, hg, rfl⟩ := hy
      intro v
      exact ⟨_, fun x => (congrFun (h.equiv τ g hg v ⟨_, rep_mem_sm M τ hg (v τ).2⟩ rfl) x).symm⟩
    | one => exact fun v => ⟨v, fun x => by rw [mul_one]⟩
    | mul a b _ _ ha hb =>
      intro v
      obtain ⟨v₁, h₁⟩ := hb v
      obtain ⟨v₂, h₂⟩ := ha v₁
      exact ⟨v₂, fun x => by rw [← mul_assoc, h₁, h₂]⟩
  intro y hy τ x
  obtain ⟨u, hu⟩ := h1 y hy v
  simp only [hu]
  refine ⟨?_, fun g hg g' hg' => ?_⟩
  · have := congrFun (h.equiv τ 1 (one_mem_UH _) u (u τ) (rep_one M τ _).symm) x
    rw [Function.update_eq_self] at this
    exact this.symm
  · have a1 := congrFun (h.equiv τ g' hg' u ⟨_, rep_mem_sm M τ hg' (u τ).2⟩ rfl) (x * atTau θ V τ g)
    have a2 := congrFun (h.equiv τ (g * g') (mul_mem_UH _ hg hg') u ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ rfl) x
    have a3 := congrFun (h.equiv τ g hg (Function.update u τ ⟨_, rep_mem_sm M τ hg' (u τ).2⟩)
      ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ (by rw [Function.update_self]; exact rep_mul M τ g hg g' hg' _)) x
    rw [Function.update_idem] at a3
    exact a1.symm.trans (a3.symm.trans a2)

theorem conj_mult : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  intro D V S S' θ M M' c hc
  classical
  have hs : ∀ τ {w : M'.H τ}, w ∈ M'.sm τ → c τ w ∈ M.sm τ := fun τ _ hw =>
    span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) hw
  refine ⟨fun τ w => ⟨hs τ, fun hw => ?_⟩, fun J χ T hT => ?_⟩
  · have := span_conj (σ := M'.rep τ) (σ' := M.rep τ) (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ).symm
      (fun g hg w => (c τ).injective (by rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply])) hw
    rwa [(c τ).symm_apply_apply] at this
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  let cs : ∀ τ, M'.sm τ → M.sm τ := fun τ w => ⟨c τ w, hs τ w.2⟩
  let cv : M'.Vec → M.Vec := fun v τ => cs τ (v τ)
  have hup : ∀ [DecidableEq D.what₂.Tau] (v : M'.Vec) τ w, cv (Function.update v τ w) = Function.update (cv v) τ (cs τ w) :=
    fun v τ w => funext fun ρ => Function.apply_update cs v τ w ρ
  let T' : MMap M' :=
    { toFun := fun v => star (T (cv v))
      map_update_add' := fun v τ x y => by
        have : cs τ (x + y) = cs τ x + cs τ y := Subtype.ext (map_add (c τ) _ _)
        rw [hup, hup, hup, this, T.map_update_add, star_add]
      map_update_smul' := fun v τ a x => by
        have : cs τ (a • x) = star a • cs τ x := Subtype.ext (map_smulₛₗ (c τ) _ _)
        rw [hup, hup, this, T.map_update_smul, star_smul, star_star] }
  have hT' : ∀ v, T' v = star (T (cv v)) := fun _ => rfl
  refine ⟨T', Submodule.subset_span ⟨fun v => isAutFunSm_star (h.aut _) (value_mem_homFun h _), fun v => ?_,
    fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v' v hv g => ?_⟩
  · intro r C hC μ 𝓕 hμ h𝓕 g
    have := h.cusp (cv v) r C hC μ 𝓕 hμ h𝓕 g
    change ∫ n in 𝓕, starRingEnd ℂ (T (cv v) ((n : GA D V) * g)) ∂μ = 0
    rw [integral_conj, this, map_zero]
  · rw [hT', Pi.star_apply, Pi.star_apply, h.lev _ k hk, star_mul']
  · rw [hT', hT', hup, h.equiv τ g hg (cv v) (cs τ w) (by change c τ w = _; rw [hw, hc τ g hg])]
    rfl
  · obtain ⟨ℓ, h1, h2⟩ := h.cont τ (cv v) x
    obtain ⟨ℓ', h3, h4⟩ := sobCont_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) h1
    refine ⟨ℓ', h3, fun w => ?_⟩
    rw [h4, hT', hup, Pi.star_apply, ← h2]
  · have : cv v' = v := funext fun τ => Subtype.ext (hv τ).symm
    rw [hT', this, Pi.star_apply]

end GlobalTheory.ConjMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem definite_unitary_cocompact :
    ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
      ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c :=
  GlobalTheory.DefiniteQuotient.exists_compact

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCarta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jm_mul_self {n : ℕ} (e : Fin n → Bool) : Formalism.REAL.Jm e * Formalism.REAL.Jm e = 1 := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem jm_injective {n : ℕ} {e e' : Fin n → Bool} (h : Formalism.REAL.Jm e = Formalism.REAL.Jm e') : e = e' := by
  funext a
  have := congrFun (congrFun h a) a
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at this
  cases he : e a <;> cases he' : e' a <;> simp_all <;> norm_num at this

theorem dsModel_of_onb_cart : ∀ (D : D7), GlobalTheory.Published.DiscreteSeriesUpqExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε) → (∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) → ∃ M : DSModel V S, cart M = C ∧ onb M = O := by
  intro D hDS V S O C h1 h2
  choose lam ε hE hP hG using h1
  choose H i1 i2 σ hσ using fun τ =>
    (GlobalTheory.Published.discreteSeriesExists_iff.1 hDS) V.rank (ε τ) (lam τ) (hP τ)
  have hdet : ∀ τ, IsUnit (O τ).det := fun τ => by
    refine Matrix.isUnit_det_of_left_inverse (B := Formalism.REAL.Jm (ε τ) * ((O τ)ᴴ * gramAt D V τ)) ?_
    rw [Matrix.mul_assoc, hG τ, jm_mul_self]
  have hr : ∀ τ, O τ * (O τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (hdet τ)
  have hl : ∀ τ, (O τ)⁻¹ * O τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
  have hii : ∀ τ, ((O τ)⁻¹)⁻¹ = O τ := fun τ => Matrix.nonsing_inv_nonsing_inv _ (hdet τ)
  let M : DSModel V S :=
    { H := H, nacg := i1, ips := i2, σ := σ, lam := lam, ε := ε, fr := fun τ => (O τ)⁻¹,
      enum := hE, ds := hσ,
      fr_unit := fun τ => (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet τ))
      fr_gram := fun τ => by
        rw [← hG τ]
        calc ((O τ)⁻¹)ᴴ * ((O τ)ᴴ * gramAt D V τ * O τ) * (O τ)⁻¹
            = (O τ * (O τ)⁻¹)ᴴ * gramAt D V τ * (O τ * (O τ)⁻¹) := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = gramAt D V τ := by rw [hr τ]; simp }
  refine ⟨M, ?_, ?_⟩
  · funext τ
    obtain ⟨e', hG', hC⟩ := h2 τ
    have he : e' = ε τ := jm_injective (by rw [← hG', hG τ])
    rw [he] at hC
    show ((O τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (O τ)⁻¹ = C τ
    rw [hii, ← hC, Matrix.mul_assoc, hr, Matrix.mul_one]
  · funext τ
    exact hii τ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemRes

theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ h : ℕ, 0 < h ∧ ∃ x : 𝓞 E, I ^ h = Ideal.span {x} := by
  have hm : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_pos, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hm⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hm (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, h2.span_singleton_generator.symm⟩

theorem exists_eq_mul_of_resS_ne_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Formalism.L2.DIV.Pl E) (ε : Formalism.L2.Herm.intAf F E) (hε : ε * ε = ε) (h : Formalism.L2.DIV.resS F P ε ≠ 1) :
    ∃ x ∈ P.asIdeal, x ≠ 0 ∧ ∃ s : Formalism.L2.Herm.intAf F E, ε = s * Formalism.L2.DIV.oToS F E x := by
  have := P.isPrime
  have h0 : Formalism.L2.DIV.resS F P ε = 0 := by
    have h1 : Formalism.L2.DIV.resS F P ε * (Formalism.L2.DIV.resS F P ε - 1) = 0 := by
      rw [mul_sub, ← map_mul, hε, mul_one, sub_self]
    exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)
  have hm : ε ∈ Formalism.L2.DIV.idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS F P.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  obtain ⟨n, hn, x, hx⟩ := exists_pow_eq_span P.asIdeal P.ne_bot
  have hp := Ideal.pow_mem_pow hm n
  have hi : ε ^ n = ε := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact IsIdempotentElem.pow_succ_eq m hε
  rw [hi, Formalism.L2.DIV.idS, ← Ideal.map_pow, hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hp
  obtain ⟨s, hs⟩ := hp
  refine ⟨x, Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x), ?_, s, hs.symm⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
  exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) ∈ _
  generalize finPart D w = z at hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem resS_idem_eq_one : ∀ (D : D7) (e : AE D) (P : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P →
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Formalism.L2.DIV.resS D.host.F P ⟨toEAf D e, h⟩ = 1 := by
  intro D e P he
  have h1 : e * e = e := he.1.1
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h1]))
  refine ⟨hint, ?_⟩
  by_contra hne
  obtain ⟨x, hxP, hx0, s, hs⟩ := exists_eq_mul_of_resS_ne_one P ⟨toEAf D e, hint⟩
    (Subtype.ext (by change toEAf D e * toEAf D e = toEAf D e; rw [← RingHom.map_mul, h1])) hne
  have hs' : toEAf D e = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (x : D.host.E) := congrArg Subtype.val hs
  refine (he.2 x hx0).1 hxP (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_)
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have h2 : toEAf D (incA D ((x : D.host.E)⁻¹)) = eToEAf D ((x : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h2, hs', mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hx0', RingHom.map_one, mul_one]
  exact s.2

end GlobalTheory.IdemRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsWeilOfEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isWeil_of_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S S' T' Tg : HSp D} (hS : S = S') (hT : Tg = T')
    {χS χT : (AE D)ˣ →* Circle} (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS χT ω') :
    ∃ ω : GlobalTheory.Grid.WRep S Tg, GlobalTheory.Grid.IsWeil ψ false S Tg χS χT ω ∧ HEq ω ω' := by
  subst hS hT
  exact ⟨ω', h, HEq.rfl⟩

theorem omCol_of_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ω ∧ HEq ω (W.om (.top t j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ t j hj
  have hS : (G.Xp j).V = G'.V (.top j) := (hSp.top j hj.le).sp
  have hT : (G.nX j).V = G'.V (.top (j + 1)) := (hSp.top (j + 1) hj).sp
  have hω := W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have hr : ∀ k, k ≤ D.R.m → Even (G'.V (.top k)).rank := fun k hk => by
    have := (G'.isV (X := .top k) hk (fun _ h => by cases h)).rank
    rw [this]; exact even_rankX D k
  have eS : G'.chrS (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrS, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr j hj.le)]
  have eT : G'.chrT (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrT, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr (j + 1) hj)]
  rw [eS, eT, hW.ψ] at hω
  exact exists_isWeil_of_eq hS hT _ hω

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_goodProjector_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  first | exact @GlobalTheory.Twist.exists_thG_models | exact GlobalTheory.Twist.exists_thG_models | (intros; apply GlobalTheory.Twist.exists_thG_models <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWrepOfEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid in

theorem exists_wrep_of_eq {D : D7} {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χ χ' : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χ χ' om) :
    ∃ ω : WRep S T, IsWeil ψ true S T χ χ' ω ∧ HEq (ω.toSgn true) om := by
  subst hS hT
  let ω : WRep S T := om.comp ((ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _))
  have e : ω.toSgn true = om := MonoidHom.ext fun x => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  unfold IsWeil
  rw [e]
  exact h

theorem core_arrows_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V, GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω ∧ HEq (ω.toSgn true) (W.om (.core i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ i hi
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := Nat.sub_le _ _
  have hom := W.om_is (.core i) (show (i + 1) ≤ D.R.m by omega)
  rw [(G'.chr_core (by omega : i + 1 ≤ D.R.m)).1, (G'.chr_core (by omega : i + 1 ≤ D.R.m)).2, hW.ψ,
    ← hSp.chi _ h1 h2] at hom
  exact exists_wrep_of_eq (hSp.core (i + 1) (by omega)).sp (hSp.core i (by omega)).sp _ _ _ _ hom

end GlobalTheory.GridJoin
end
end

