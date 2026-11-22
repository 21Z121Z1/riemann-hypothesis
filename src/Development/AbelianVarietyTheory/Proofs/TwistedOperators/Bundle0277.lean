import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.LinRed
open scoped InnerProductSpace

namespace GlobalTheory.LeviDense

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

private theorem exists_iteratedDeriv_inner_semigroup_eq {T : ℝ → V →L[ℂ] V} (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0) (w : V) (k : ℕ) :
    ∀ v ∈ S, ∃ u ∈ S, iteratedDeriv k (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t u⟫_ℂ := by
  induction k with
  | zero => intro v hv; exact ⟨v, hv, by simp⟩
  | succ k ih =>
    intro v hv
    obtain ⟨v', hv', hder⟩ := hd v hv
    have hderiv : deriv (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t v'⟫_ℂ := by
      funext t
      have h3 : HasDerivAt (fun s => T (s - t) v) v' t :=
        HasDerivAt.comp_sub_const (f := fun s => T s v) t t (by rw [sub_self]; exact hder)
      have h2 : HasDerivAt (fun s => T t (T (s - t) v)) (T t v') t :=
        ((T t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3
      have h1 : HasDerivAt (fun s => T s v) (T t v') t := by
        refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        show T s v = T t (T (s - t) v)
        rw [← ContinuousLinearMap.comp_apply, ← hT, add_sub_cancel]
      exact ((((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1)).deriv
    obtain ⟨u, hu, hk⟩ := ih v' hv'
    exact ⟨u, hu, by rw [iteratedDeriv_succ', hderiv, hk]⟩

theorem oneParameter_mem_closure {T : ℝ → V →L[ℂ] V} (h0 : T 0 = 1) (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0)
    (ha : ∀ v ∈ S, ∀ w, AnalyticOnNhd ℝ (fun t => ⟪w, T t v⟫_ℂ) Set.univ) (t : ℝ) :
    ∀ v ∈ S.topologicalClosure, T t v ∈ S.topologicalClosure := by
  have key : ∀ v ∈ S, T t v ∈ S.topologicalClosure := by
    intro v hv
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    have hf := ha v hv w
    have hall : ∀ k, iteratedDeriv k (fun s => ⟪w, T s v⟫_ℂ) 0 = 0 := by
      intro k
      obtain ⟨u, hu, hk⟩ := exists_iteratedDeriv_inner_semigroup_eq hT hd w k v hv
      rw [hk]
      simp only [h0, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal hu hw
    have htop : analyticOrderAt (fun s => ⟪w, T s v⟫_ℂ) 0 = ⊤ := by
      by_contra hne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
      have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := m + 1)
        (hf 0 (Set.mem_univ _))).2 (fun i _ => hall i)
      rw [← hm] at hle
      have : m + 1 ≤ m := by exact_mod_cast hle
      omega
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
      (analyticOrderAt_eq_top.1 htop) (Set.mem_univ t)
  intro x hx
  have hcl : IsClosed ((T t) ⁻¹' (S.topologicalClosure : Set V)) :=
    S.isClosed_topologicalClosure.preimage (T t).continuous
  have hx' : x ∈ closure (S : Set V) := by rw [← Submodule.topologicalClosure_coe]; exact hx
  exact closure_minimal (fun v hv => key v hv) hcl hx'

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem analytic_exp {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : AnalyticOnGroup G f) {X : Matrix (Fin n) (Fin n) ℂ} (hX : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) :
    AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp (t • X))) Set.univ := by
  intro t₀ _
  obtain ⟨U, F, hUo, hgU, hF, hfF⟩ := hf _ (hX t₀)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hL : ∀ A, L A = Matrix.of.symm A := fun _ => rfl
  have hE : AnalyticAt ℝ (fun t : ℝ => L (NormedSpace.exp (t • X))) t₀ :=
    L.analyticAt _ |>.comp ((NormedSpace.exp_analytic (𝕂 := ℝ) _).comp
      ((analyticAt_id).smul analyticAt_const))
  have hE' : AnalyticAt ℝ (fun t : ℝ => F (L (NormedSpace.exp (t • X)))) t₀ :=
    (hF _ (by rw [hL]; exact hgU)).comp hE
  have hev : ∀ᶠ t in nhds t₀, L (NormedSpace.exp (t • X)) ∈ U :=
    hE.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hL]; exact hgU))
  refine hE'.congr (hev.mono fun t ht => ?_)
  have h1 := hfF _ ht (by rw [hL, Equiv.apply_symm_apply]; exact hX t)
  rw [hL, Equiv.apply_symm_apply] at h1
  exact h1.symm

private theorem mul_Jm_comm_of_unitary_of_preserves {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hu : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (hJ : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) :
    A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
  have h2 : A * Aᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.1 hu
  calc A * Formalism.REAL.Jm ε = A * (Aᴴ * Formalism.REAL.Jm ε * A) := by rw [hJ]
    _ = (A * Aᴴ) * Formalism.REAL.Jm ε * A := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * A := by rw [h2, Matrix.one_mul]

end

omit [CompleteSpace V] in

theorem isKFinOn_of_isKFinIn {n : ℕ} {ε : Fin n → Bool} {M : Subgroup (UJ ε)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} {v : V} (h : IsKFinIn M σ v) : IsKFinOn (mats M) σ v := by
  obtain ⟨U, hU, hv, hk⟩ := h
  refine ⟨U, hU, hv, ?_⟩
  rintro _ ⟨⟨g, hgM, rfl⟩, hgu⟩ w hw
  refine hk g (Subgroup.mem_inf.2 ⟨?_, hgM⟩) w hw
  show toM g ∈ Kset ε
  show toM g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toM g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * toM g
  exact ⟨hgu, mul_Jm_comm_of_unitary_of_preserves ε hgu g.2⟩

theorem leviSubmoduleDense (hadm : GlobalTheory.Published.IrreducibleUnitaryAdmissible)
    (han : GlobalTheory.Published.KFiniteCoefficientsAnalytic) : GlobalTheory.Published.LeviSubmoduleDense := by
  intro n ε a j W hW hj V _ _ _ σ hU hI S hS hK hD
  obtain ⟨hLR, hdec⟩ := GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp n ε a j W hW hj
  have hadmG : GlobalTheory.LinRed.IsAdmOn (mats (leviOne ε W)) σ := hadm n _ hLR V σ hU hI
  have hexp : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
      ∀ x ∈ S.topologicalClosure, σ (NormedSpace.exp X) x ∈ S.topologicalClosure := by
    intro X hX x hx
    have h1 := oneParameter_mem_closure (T := fun t : ℝ => σ (NormedSpace.exp (t • X))) ?_ ?_ (hD X hX) ?_ 1 x hx
    · simpa using h1
    · simp only [zero_smul, NormedSpace.exp_zero]
      exact hU.1.1
    · intro s t
      show σ (NormedSpace.exp ((s + t) • X)) = σ (NormedSpace.exp (s • X)) ∘L σ (NormedSpace.exp (t • X))
      rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]
      exact hU.1.2 _ (hX s) _ (hX t)
    · intro v hv w
      exact analytic_exp (han n _ hLR V σ hadmG v w (isKFinOn_of_isKFinIn (hK v hv))) hX
  have hinv : ∀ g ∈ mats (leviOne ε W), ∀ x ∈ S.topologicalClosure, σ g x ∈ S.topologicalClosure := by
    intro g hg x hx
    obtain ⟨X, Y, hX, hY, rfl⟩ := hdec g hg
    have hX1 : NormedSpace.exp X ∈ mats (leviOne ε W) := by simpa using hX 1
    have hY1 : NormedSpace.exp Y ∈ mats (leviOne ε W) := by simpa using hY 1
    rw [hU.1.2 _ hX1 _ hY1, ContinuousLinearMap.comp_apply]
    exact hexp X hX _ (hexp Y hY x hx)
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure hinv with h | h
  · have hle := S.le_topologicalClosure
    rw [h] at hle
    exact absurd (eq_bot_iff.2 hle) hS
  · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, h, Submodule.top_coe]

end GlobalTheory.LeviDense

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LinkInvTheta

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem map_starAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {x : WO L S} (hx : x.map φ = 0) : (starAdj L S x).map φ = 0 := by
  have h1 : (adj x).map φ = 0 := by
    funext i j
    exact hφ (x j i) (congrFun (congrFun hx j) i)
  have h2 := map_mul_eq_zero_right φ (giA L) (map_mul_eq_zero_left φ h1 (gA S))
  funext i j
  have h3 : φ ((giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D D.host.xi0 * (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

theorem continuous_starAdj (L S : HSp D) : Continuous (starAdj L S) := by
  have h1 : Continuous fun x : WO L S => (adj x ⬝ gA S : Mx D L.rank S.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun x : WO L S => (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D D.host.xi0)

theorem starAdj_mem (L S : HSp D) {x : WO L S} (hx : x ∈ ratMx D S.rank L.rank) :
    starAdj L S x ∈ ratMx D L.rank S.rank := by
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hx
  rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
  exact rat_mem _

theorem lnk_simil {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Lnk L ζ L' ζ') : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

theorem link_inv_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  intro D ψ hψ L L' S ζ ζ' hL hL' l
  have hτ := lnk_simil hL' l
  refine ⟨hτ, fun Φ₀ hΦ => ?_⟩
  have hτ' : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hτ
  obtain ⟨hadd, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L' S l.τ 1 hτ' (l.κ S) (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (l.κ S w) (l.κ S w') = -symplOH S L' w w' := fun w w' => by
    unfold symplOH; rw [hsym]; push_cast; ring
  have hτ0 : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : ζ = 0 := neg_eq_zero.mp e.symm
    apply hL.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one hL.1 hL'.1 l.τ hτ0
  let g : WO L S → WO S L' := fun x => (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x
  have hgk : ∀ w, g (l.κ S w) = w := by
    intro w
    show (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S (l.κ S w) = w
    rw [Lnk.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  have hkg : ∀ x, l.κ S (g x) = x := by
    intro x
    show l.κ S ((rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x) = x
    rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]
  have gadd : ∀ x y, g (x + y) = g x + g y := fun x y => by
    conv_lhs => rw [← hkg x, ← hkg y, ← hadd, hgk]
  have gH : ∀ x y, symplOH S L' (g x) (g y) = -symplOH L S x y := fun x y => by
    conv_rhs => rw [← hkg x, ← hkg y, hH, neg_neg]
  have gcont : Continuous g := continuous_const.matrix_mul (continuous_starAdj L S)
  have grat : ∀ x ∈ ratMx D S.rank L.rank, g x ∈ ratMx D L'.rank S.rank := fun x hx =>
    ratMx_mul (rat_mem σ) (starAdj_mem L S hx)
  have gfin : ∀ x : WO L S, x.map (finPart D) = 0 → (g x).map (finPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (finPart D) _
      (map_starAdj_eq_zero (finPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.finPart_conj, hz, map_zero]) L S h)
  have ginf : ∀ x : WO L S, x.map (infPart D) = 0 → (g x).map (infPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (infPart D) _
      (map_starAdj_eq_zero (infPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.infPart_conj, hz, map_zero]) L S h)
  let A : WO L S →+ WO S L' := AddMonoidHom.mk' g gadd
  refine ⟨fun x => star (Φ₀ (g x)), ⟨fun γ x => ?_, ?_, continuous_star.comp (hΦ.cont.comp gcont), fun k M h1 h2 x => ?_⟩, ?_⟩
  · obtain ⟨γ', hγ'⟩ := grat (ratW S L γ) ⟨γ, rfl⟩
    have e : g (ratW S L γ) = ratW L' S γ' := hγ'.symm
    show star (Φ₀ (g (ratW S L γ + x))) = ψ (-(symplOH L S (ratW S L γ) x)) * star (Φ₀ (g x))
    rw [gadd, e, hΦ.quasi, star_mul', star_psi hψ, ← e, gH, neg_neg]
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U.comap A, hU.preimage gcont, fun u hu h0 => ?_⟩
    funext x
    have e := congrFun (h _ hu (ginf u h0)) (g x)
    unfold heisO at e ⊢
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = star (Φ₀ (g x))
    rw [← e, star_mul', star_psi hψ]
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = ψ (-symplOH S L' (g x) (g u)) * star (Φ₀ (g x + g u))
    rw [gH, neg_neg, gadd]
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => gfin (M t) (h2 t)
    have := hΦ.smooth k (A.comp M) (gcont.comp h1) h3 (g x)
    have heq : (fun t => Φ₀ (g (x + M t))) = fun t => Φ₀ (g x + A (M t)) :=
      funext fun t => congrArg Φ₀ (gadd x (M t))
    have h4 := (congrArg (ContDiff ℝ _) heq).mpr this
    exact Complex.conjCLE.contDiff.comp h4
  · funext w
    show Φ₀ w = star (star (Φ₀ (g (l.κ S w))))
    rw [hgk, star_star]
end GlobalTheory.LinkInvTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def cplx {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (z : Mx D 1 k) :
    WO V W :=
  ∑ i, z 0 i • (B i).map (incA D)

section

variable {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E)

theorem cplx_add (z z' : Mx D 1 k) : cplx V W B (z + z') = cplx V W B z + cplx V W B z' := by
  simp only [cplx, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem cplx_zero : cplx V W B 0 = 0 := by
  simp [cplx]

theorem continuous_cplx : Continuous (cplx V W B) := by
  unfold cplx
  refine continuous_finset_sum _ fun i _ => ?_
  exact (continuous_id.matrix_elem 0 i).smul continuous_const

theorem cplx_rat (c : Matrix (Fin 1) (Fin k) D.host.E) :
    cplx V W B (c.map (incA D)) = (∑ i, c 0 i • B i).map (incA D) := by
  ext p q
  simp [cplx, Matrix.sum_apply, map_sum, smul_eq_mul]

end

theorem symplO_eq_add {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem meanX_heisO_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) (hx : ∀ y, symplO V W x (emb V W P Q y) = 0) :
    meanX V W P Q μ 𝓨 (heisO ψ V W w F) x = ψ (symplO V W x w) * meanX V W P Q μ 𝓨 F x := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  obtain ⟨γ, rfl⟩ := hw
  unfold meanX
  rw [← integral_const_mul]
  congr 1
  funext y
  have hq := hF.quasi γ (emb V W P Q y + x)
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  simp only [heisO]
  rw [er] at hwX ⊢
  rw [show emb V W P Q y + x + ratW W V γ = ratW W V γ + (emb V W P Q y + x) by abel, hq, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [l1, l2, skew (ratW W V γ) (emb V W P Q y), hH0 _ _ (hwX y), skew (ratW W V γ) x, symplO_eq_add, skew (ratW W V γ) x]
  ring

theorem meanX_mul_star_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (F F' : WO V W → ℂ) (hF : IsThetaFunO ψ V W F)
    (hF' : IsThetaFunO ψ V W F') (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) :
    meanX V W P Q μ 𝓨 F (w + x) * star (meanX V W P Q μ 𝓨 F' (w + x)) =
      meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x) := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  obtain ⟨γ, rfl⟩ := hw
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  rw [er] at hwX ⊢
  have key : ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G →
      meanX V W P Q μ 𝓨 G (ratW W V γ + x) = ψ (-(symplOH V W (ratW W V γ) x)) * meanX V W P Q μ 𝓨 G x := by
    intro G hG
    unfold meanX
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [show emb V W P Q y + (ratW W V γ + x) = ratW W V γ + (emb V W P Q y + x) by abel, hG.quasi, l2,
      hH0 _ _ (hwX y), zero_add]
  rw [key F hF, key F' hF', star_mul]
  have hn : ψ (-(symplOH V W (ratW W V γ) x)) * star (ψ (-(symplOH V W (ratW W V γ) x))) = 1 := by
    have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ) x))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  linear_combination (meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x)) * hn

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatAStdLIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TensColRead

variable {D : D7}

def embInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem embInf_add_emb (w : AE D) :
    embInf D (Formalism.L2.Theta.infPart D w) + GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add]
    conv_rhs => rw [← ha, ← hb]
    abel
  | tmul a e =>
    have e1 : embInf D (Formalism.L2.Theta.infPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F (fstA D.host.F a) 0) ⊗ₜ[D.host.F] e := rfl
    have e2 : GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F 0 (sndA D.host.F a)) ⊗ₜ[D.host.F] e := rfl
    rw [e1, e2, ← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _)

theorem emb_finPart (w : AE D) (h : Formalism.L2.Theta.infPart D w = 0) :
    GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  have := embInf_add_emb w
  rwa [h, map_zero, zero_add] at this

theorem col_iff {S T : HSp D} (L : Lt D.host.E T.rank) (x : WO S T) (k : Fin S.rank) :
    (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L ↔
      (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  GlobalTheory.LevSplit.latHat_iff L _

def colHom (S T : HSp D) (k : Fin S.rank) : WO S T →+ (Fin T.rank → AfE D) where
  toFun x := fun c => Formalism.L2.Theta.finPart D (x c k)
  map_zero' := by funext c; simp
  map_add' x y := by funext c; simp

theorem toAf_single_mem (n : ℕ) (k : Fin n) : toAf (Pi.single k (1 : D.host.E)) ∈ hatV (stdL D.host.E n) :=
  AddSubgroup.subset_closure ⟨1, GlobalTheory.TensLatMove.intAf_one, Pi.single k 1,
    Submodule.subset_span ⟨k, rfl⟩, rfl⟩

theorem mem_hatA_stdL_iff : ∀ (D : D7) (S T : HSp D) (L : Lt D.host.E T.rank) (x : WO S T), IsFinPt x → (x ∈ hatA S T (tens (stdL D.host.E S.rank) L) ↔ ∀ k : Fin S.rank, (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L) := by
  intro D S T L x hx
  constructor
  · intro hmem k
    rw [← col_iff]
    have hle : hatA S T (tens (stdL D.host.E S.rank) L) ≤ (hatV L).comap (colHom S T k) := by
      rw [hatA, AddSubgroup.closure_le]
      rintro _ ⟨α, hα, y, hy, rfl⟩
      exact AddSubgroup.subset_closure ⟨α, hα, y k, (GlobalTheory.SW.TensLat.mem_tens_stdL L y).1 hy k, rfl⟩
    exact hle hmem
  · intro h
    have hu : ∀ k, (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L := fun k => (col_iff L x k).2 (h k)
    have e : x = ∑ k, GlobalTheory.TensLatMove.outer S T (toAf (Pi.single k 1)) (fun c => Formalism.L2.Theta.finPart D (x c k)) := by
      ext c k'
      have hc : Formalism.L2.Theta.infPart D (x c k') = 0 := by
        have := congrFun (congrFun hx c) k'
        simpa using this
      rw [Matrix.sum_apply]
      simp only [GlobalTheory.TensLatMove.outer, Matrix.of_apply, toAf]
      rw [← map_sum, Finset.sum_eq_single k']
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]
        exact (emb_finPart _ hc).symm
      · intro j _ hj
        rw [Pi.single_eq_of_ne (Ne.symm hj), TensorProduct.tmul_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ k') h'
    rw [e]
    exact sum_mem fun k _ => GlobalTheory.TensLatMove.outer_mem S T _ L _ (toAf_single_mem _ k) _ (hu k)

end GlobalTheory.TensColRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  first | exact @GlobalTheory.CoverModel.modelsAreCoverSeries_all | exact GlobalTheory.CoverModel.modelsAreCoverSeries_all | (intros; apply GlobalTheory.CoverModel.modelsAreCoverSeries_all <;> assumption)
end

