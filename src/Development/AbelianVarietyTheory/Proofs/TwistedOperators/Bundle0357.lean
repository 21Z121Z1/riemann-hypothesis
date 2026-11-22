import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0283
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0340
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfiniteHeightTransposeGramUnitaryLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HtInfKapX

open GlobalTheory.AdelicU (htInf htOf normInf opNorm compInf)

theorem opNorm_reindex_le {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) ≤ opNorm y := by
  unfold GlobalTheory.AdelicU.opNorm
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  let c : EuclideanSpace ℂ m → EuclideanSpace ℂ n := fun z => WithLp.toLp 2 fun i => z (e i)
  let c' : EuclideanSpace ℂ n → EuclideanSpace ℂ m := fun z => WithLp.toLp 2 fun j => z (e.symm j)
  have hc : ∀ z, ‖c z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c]
    congr 1
    exact Equiv.sum_comp e (fun j => ‖z j‖₊ ^ 2)
  have hc' : ∀ z, ‖c' z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c']
    congr 1
    exact Equiv.sum_comp e.symm (fun j => ‖z j‖₊ ^ 2)
  have h : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) (reindex e e y) x =
      c' (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (c x)) := by
    ext j
    change ∑ k, y (e.symm j) (e.symm k) * x k = ∑ i, y (e.symm j) i * x (e i)
    rw [← Equiv.sum_comp e]
    simp
  rw [h, hc', ← hc x]
  exact ContinuousLinearMap.le_opNNNorm _ _

theorem opNorm_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) = opNorm y := by
  refine le_antisymm (opNorm_reindex_le e y) ?_
  have h : reindex e.symm e.symm (reindex e e y) = y := by ext; simp
  calc opNorm y = opNorm (reindex e.symm e.symm (reindex e e y)) := by rw [h]
    _ ≤ opNorm (reindex e e y) := opNorm_reindex_le e.symm _

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (w : NumberField.InfinitePlace F)

theorem normInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n (w.Completion ⊗[F] E)) : normInf F w (reindex e e y) = normInf F w y := by
  unfold GlobalTheory.AdelicU.normInf
  congr 1
  funext τ
  rw [reindex_apply, ← Matrix.submatrix_map, ← reindex_apply, opNorm_reindex]

theorem htInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : (Matrix n n (w.Completion ⊗[F] E))ˣ) :
    htInf F w (Units.map (Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e).toMonoidHom g) =
      htInf F w g := by
  have key : ∀ y, normInf F w ((Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e) y) =
      normInf F w y := fun y => by rw [Matrix.reindexAlgEquiv_apply, normInf_reindex]
  show GlobalTheory.AdelicU.htOf (normInf F w) _ = GlobalTheory.AdelicU.htOf (normInf F w) _
  rw [GlobalTheory.AdelicU.htOf, GlobalTheory.AdelicU.htOf, ← map_inv, Units.coe_map, Units.coe_map]
  exact congrArg₂ _ rfl (congrArg₂ _ (key _) (key _))

theorem bc_reindex {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (g : (Matrix n n A)ˣ) :
    Formalism.UG.bc φ (Units.map (Matrix.reindexAlgEquiv A A e).toMonoidHom g) =
      Units.map (Matrix.reindexAlgEquiv B B e).toMonoidHom (Formalism.UG.bc φ g) := by
  ext i j
  rfl

theorem htInf_kapX_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  intro D θ hθ X d e J hJ
  refine ⟨1, fun h => ?_⟩
  rw [one_mul]
  refine le_of_eq ?_
  have key : ∀ w, GlobalTheory.AdelicU.htInf D.host.F w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) =
      GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom X h)) :=
    fun w => by
      show GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc _
        (Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (Formalism.L2.Theta.matHom X h))) = _
      rw [bc_reindex, htInf_reindex]
  simp only [key]
  exact (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
    (Finset.prod_congr rfl fun τ _ => GlobalTheory.Grow.htInf_eq_infHt X hθ τ h)

end GlobalTheory.HtInfKapX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitesimalCharacterDifference
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.IndCap

theorem epow_eq_pow' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp [epow, pow_succ, Matrix.mul_apply, ih]

theorem etr_succ_eq_gelfA' {B : Type} [Ring B] [Algebra ℂ B] {n : ℕ} (E : Fin n → Fin n → B) (k : ℕ) :
    etr E (k + 1) = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]; simp [etr, epow_eq_pow']

theorem commute_epow' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (z : B)
    (hz : ∀ a b, Commute z (E a b)) (m : ℕ) (a b : Fin n) : Commute z (epow E m a b) := by
  induction m generalizing a b with
  | zero => simp only [epow]; split_ifs <;> simp
  | succ m ih => simp only [epow]; exact Commute.sum_right _ _ _ fun c _ => (ih a c).mul_right (hz c b)

theorem commute_etr' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (z : B)
    (hz : ∀ a b, Commute z (E a b)) (m : ℕ) : Commute z (etr E m) :=
  Commute.sum_right _ _ _ fun a _ => commute_epow' E z hz m a a

theorem lift_etr' {n : ℕ} {B : Type} [Ring B] [Algebra ℂ B] (φ : Fin n × Fin n → B) (m : ℕ) :
    FreeAlgebra.lift ℂ φ (etr (Egl n) m) = etr (fun a b => φ (a, b)) m := by
  have key : ∀ a b, FreeAlgebra.lift ℂ φ (epow (Egl n) m a b) = epow (fun a b => φ (a, b)) m a b := by
    induction m with
    | zero => intro a b; simp only [epow]; split_ifs <;> simp
    | succ m ih => intro a b; simp [epow, map_sum, map_mul, ih, Egl]
  simp [etr, map_sum, key]

section Restr
variable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (V : Submodule ℂ M)
  (E : Fin n → Fin n → Module.End ℂ M) (hE : ∀ a b, ∀ v ∈ V, E a b v ∈ V)

theorem epow_restrict' (m : ℕ) (a b : Fin n) (v : V) :
    ((epow (fun a b => (E a b).restrict (hE a b)) m a b v : V) : M) = epow E m a b v := by
  induction m generalizing a b v with
  | zero => simp only [epow]; split_ifs <;> simp
  | succ m ih =>
    simp only [epow, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, ih]
    rfl

theorem glRel_restrict' (h : GlRel E) : GlRel (fun a b => (E a b).restrict (hE a b)) := by
  intro a b c d
  ext v
  have := congrArg (fun F => F (v : M)) (h a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, LinearMap.restrict_apply]
  rw [this]
  split_ifs <;> simp
end Restr

theorem infChar_sub_eq_of_line : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ χ : Fin n → ℂ, (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ i j, i ≠ j ∧ χ i - χ j = I.s ⟨0, h⟩ := by
  intro hLC n ε I h hj χ hnil
  obtain ⟨hInd, -⟩ := hLC
  obtain ⟨hadm, -, hgk, -⟩ := hInd n ε I
  obtain ⟨A, hA1, hA2, hA3, hA4, -⟩ := GlobalTheory.T.gl_relations_on_k_finite_vectors n ε I.H I.ρ hadm hgk
  set E0 : Fin n → Fin n → Module.End ℂ (kFinVec ε I.ρ) := fun a b => A (Matrix.single a b 1) with hE0
  have hGl0 : GlRel E0 := by simpa using (hA2 1 isUnit_one).1
  set T : ℕ → Module.End ℂ (kFinVec ε I.ρ) := fun k => etr E0 (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1)) with hT
  have hcommE : ∀ k a b, Commute (etr E0 (k + 1)) (E0 a b) := fun k a b => by
    rw [etr_succ_eq_gelfA']; exact (GlobalTheory.SmoothForms.commute_gelfA _ n E0 hGl0 k a b).symm
  have hcommTE : ∀ k a b, Commute (T k) (E0 a b) := fun k a b =>
    (hcommE k a b).sub_left (Algebra.commute_algebraMap_left _ _)
  have hTcomm : ∀ k l, Commute (T k) (T l) := fun k l =>
    ((commute_etr' E0 _ (hcommTE k) (l + 1))).sub_right (Algebra.commute_algebraMap_right _ _)
  have hnilT : ∀ k (v : kFinVec ε I.ρ), ∃ N : ℕ, (T k ^ N) v = 0 := fun k v => by
    obtain ⟨N, hN⟩ := hnil k v v.2
    refine ⟨N, ?_⟩
    rw [hA3] at hN
    have e : FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1))
        ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) = T k ^ N := by
      rw [map_pow, map_sub, AlgHom.commutes, lift_etr']
    rw [e] at hN
    exact Subtype.ext (by simpa using hN)
  have hTK : ∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε I.ρ), (w : I.H) = I.ρ κ v →
      ((T k w : kFinVec ε I.ρ) : I.H) = I.ρ κ (T k v : I.H) := fun κ hκ k v w hw => by
    have := hA4 κ hκ (k + 1) v w hw
    simp only [hT, LinearMap.sub_apply, Submodule.coe_sub, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, Submodule.coe_smul, this, hw, map_sub, map_smul]
  haveI : Nontrivial I.H := GlobalTheory.T.induced_module_nontrivial n ε I
  obtain ⟨S, hSfd, hS0, hST⟩ := GlobalTheory.T.finite_dimensional_invariant_subspace n ε I.H I.ρ hadm T hTK
  obtain ⟨v₀, -, hv₀, hv₀T⟩ := GlobalTheory.T.common_kernel_commuting_nilpotent _ T S hSfd hS0 hST hTcomm (fun k v _ => hnilT k v)
  set Y : Submodule ℂ (kFinVec ε I.ρ) := ⨅ k : ℕ, LinearMap.ker (T k) with hY
  have memY : ∀ w, w ∈ Y ↔ ∀ k, T k w = 0 := fun w => by simp [hY, Submodule.mem_iInf]
  have hYE : ∀ a b, ∀ w ∈ Y, E0 a b w ∈ Y := fun a b w hw => (memY _).2 fun k => by
    rw [← Module.End.mul_apply, (hcommTE k a b).eq, Module.End.mul_apply, (memY w).1 hw k, map_zero]
  have hYA : ∀ Z : Matrix (Fin n) (Fin n) ℂ, ∀ w ∈ Y, A Z w ∈ Y := fun Z w hw => by
    rw [Matrix.matrix_eq_sum_single Z]
    simp only [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    rw [show Matrix.single a b (Z a b) = Z a b • Matrix.single a b 1 by simp [Matrix.smul_single], map_smul,
      LinearMap.smul_apply]
    exact Y.smul_mem _ (hYE a b w hw)

  have hv₀Y : v₀ ∈ Y := (memY v₀).2 hv₀T
  set Y' : Submodule ℂ I.H := Y.map (kFinVec ε I.ρ).subtype with hY'
  have hY'le : Y' ≤ kFinVec ε I.ρ := Submodule.map_subtype_le _ _
  have hY'0 : Y' ≠ ⊥ := by
    intro e
    have : ((v₀ : kFinVec ε I.ρ) : I.H) ∈ Y' := Submodule.mem_map_of_mem hv₀Y
    rw [e, Submodule.mem_bot] at this
    exact hv₀ (Subtype.ext this)
  have hY'K : IsKStableOn ε I.ρ Y' := by
    rintro g hg _ ⟨w, hw, rfl⟩
    have hm : I.ρ g (w : I.H) ∈ kFinVec ε I.ρ := isKStableOn_kFinVec ε I.ρ g hg _ w.2
    refine ⟨⟨_, hm⟩, (memY _).2 fun k => Subtype.ext ?_, rfl⟩
    rw [hTK g hg k w ⟨_, hm⟩ rfl, (memY w).1 hw k]
    simp

  have hW1 : Module.finrank ℂ (I.W ⟨1, Nat.succ_lt_succ h⟩) = 1 := by
    have := I.flag.2.2.1 ⟨0, h⟩
    have hz : Module.finrank ℂ (I.W (⟨0, h⟩ : Fin I.a).castSucc) = 0 := Submodule.finrank_eq_zero.2 I.flag.1
    rw [hz, hj] at this
    exact this.trans (zero_add 1)
  obtain ⟨e, he1, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hW1.ge)
  have hiso : star e ⬝ᵥ (Jm ε *ᵥ e) = 0 := by
    have hl : e ∈ I.W (Fin.last I.a) := I.flag.2.1 (Fin.le_last _) he1
    exact I.flag.2.2.2 e hl e hl
  obtain ⟨P, p, q, c, hPu, hpq, hPe, hPe', hG⟩ := GlobalTheory.T.hyperbolic_pair_change_of_basis n ε e he0 hiso
  have hPe1 : P *ᵥ Pi.single p 1 ∈ I.W ⟨1, Nat.succ_lt_succ h⟩ := hPe ▸ he1
  have hPe'' : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) := by rw [hPe]; exact hPe'
  obtain ⟨hOffp, hOffq⟩ := GlobalTheory.T.hyperbolic_pair_in_first_flag_space n ε I.a I.j I.W h I.flag hj P p q c hPu hpq hPe1 hPe'' hG
  obtain ⟨hH₀, hsplit, hTc, hTcc⟩ := GlobalTheory.T.hyperbolic_pair_split_torus n ε I.a I.j I.W h I.flag hj P p q c hPu hpq hPe1 hPe'' hG
  set H₀ := P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹ with hH₀def
  set Tc := P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹ with hTcdef
  obtain ⟨ℓ, γ, ⟨y, hyY, hy⟩, hℓN, hℓH, hℓT⟩ := GlobalTheory.T.k_stable_subspace_exponent_functional hInd n ε I h hj H₀ Tc hH₀ hTc hsplit hTcc Y' hY'le hY'0 hY'K

  set E' : Fin n → Fin n → Module.End ℂ Y := fun a b => (A (P * Matrix.single a b 1 * P⁻¹)).restrict
    (fun w hw => hYA _ w hw) with hE'
  have hGl' : GlRel E' := glRel_restrict' Y _ _ (hA2 P hPu).1
  have hetr' : ∀ (k : ℕ) (v : Y), etr E' (k + 1) v = gelfVal χ (k + 1) • v := fun k v => by
    apply Subtype.ext
    have e1 : ((etr E' (k + 1) v : Y) : kFinVec ε I.ρ) = etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) (k + 1) v := by
      simp only [etr, LinearMap.sum_apply, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun a _ => epow_restrict' Y _ _ (k + 1) a a v
    rw [e1, (hA2 P hPu).2]
    have := (memY v).1 v.2 k
    simp only [hT, LinearMap.sub_apply, sub_eq_zero, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; rfl
  have hqdet := GlobalTheory.T.qdet_apply_eq_prod_of_gelfVal Y n E' χ hGl' hetr'
  set ℓ' : Y →ₗ[ℂ] ℂ := ℓ ∘ₗ (kFinVec ε I.ρ).subtype ∘ₗ Y.subtype with hℓ'
  have hℓ'0 : ℓ' ≠ 0 := by
    obtain ⟨w, hw, rfl⟩ := hyY
    intro e0
    exact hy (by simpa [hℓ'] using LinearMap.congr_fun e0 ⟨w, hw⟩)

  have hE'v : ∀ a b (v : Y), ℓ' (E' a b v) =
      ℓ ((A (P * Matrix.single a b 1 * P⁻¹) (v : kFinVec ε I.ρ) : kFinVec ε I.ρ) : I.H) := fun a b v => rfl
  have hℓ'v : ∀ v : Y, ℓ' v = ℓ ((v : kFinVec ε I.ρ) : I.H) := fun v => rfl
  have hsplitA : ∀ (X X' : Matrix (Fin n) (Fin n) ℂ) (u v : ℂ) (w : Y), X ∈ lieSet ε → X' ∈ lieSet ε →
      ℓ ((A (u • X + v • X') (w : kFinVec ε I.ρ) : kFinVec ε I.ρ) : I.H) =
        u * ℓ (dRep I.ρ X ((w : kFinVec ε I.ρ) : I.H)) + v * ℓ (dRep I.ρ X' ((w : kFinVec ε I.ρ) : I.H)) := by
    intro X X' u v w hX hX'
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add, map_smul, map_smul, hA1 X hX, hA1 X' hX',
      smul_eq_mul, smul_eq_mul]
  have hoffp : ∀ b, b ≠ p → ∀ v : Y, ℓ' (E' p b v) = 0 := fun b hb v => by
    obtain ⟨X, X', hX, hX', hXN, hX'N, he⟩ := hOffp b hb
    rw [hE'v, he, show X + Complex.I • X' = (1 : ℂ) • X + Complex.I • X' by rw [one_smul], hsplitA X X' _ _ v hX hX',
      hℓN X hX hXN _ (v : kFinVec ε I.ρ).2, hℓN X' hX' hX'N _ (v : kFinVec ε I.ρ).2]
    simp
  have hoffq : ∀ b, b ≠ q → ∀ v : Y, ℓ' (E' b q v) = 0 := fun b hb v => by
    obtain ⟨X, X', hX, hX', hXN, hX'N, he⟩ := hOffq b hb
    rw [hE'v, he, show X + Complex.I • X' = (1 : ℂ) • X + Complex.I • X' by rw [one_smul], hsplitA X X' _ _ v hX hX',
      hℓN X hX hXN _ (v : kFinVec ε I.ρ).2, hℓN X' hX' hX'N _ (v : kFinVec ε I.ρ).2]
    simp
  have hdiag : ∀ (u v : ℂ) (r : Fin n), (∀ i, diagonal (Pi.single r (1 : ℂ)) i i =
      u * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) i + v * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) i) →
      P * Matrix.single r r 1 * P⁻¹ = u • H₀ + v • Tc := by
    intro u v r hr
    have e : Matrix.single r r (1 : ℂ) = u • diagonal (Pi.single p 1 - Pi.single q 1) +
        v • diagonal (Pi.single p Complex.I + Pi.single q Complex.I) := by
      ext i k
      by_cases hik : i = k
      · subst hik
        have := hr i
        simp only [diagonal_apply_eq] at this
        simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]
        rw [← this, Matrix.single_apply, Pi.single_apply]
        by_cases h' : r = i <;> simp [h', eq_comm]
      · have hn : ¬ (r = i ∧ r = k) := fun hh => hik (hh.1 ▸ hh.2)
        simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_ne _ hik, smul_zero, add_zero]
        rw [Matrix.single_apply, if_neg hn]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
  have hDp : P * Matrix.single p p 1 * P⁻¹ = (1 / 2 : ℂ) • H₀ + (-(Complex.I / 2)) • Tc := hdiag _ _ p fun i => by
    by_cases hi : i = p
    · subst hi; simp [Pi.single_apply, hpq.symm]; ring_nf; rw [Complex.I_sq]; ring
    · by_cases hi' : i = q
      · subst hi'; simp [Pi.single_apply, hi]; ring_nf; rw [Complex.I_sq]; ring
      · simp [Pi.single_apply, hi, hi']
  have hDq : P * Matrix.single q q 1 * P⁻¹ = (-(1 / 2) : ℂ) • H₀ + (-(Complex.I / 2)) • Tc := hdiag _ _ q fun i => by
    by_cases hi : i = p
    · subst hi; simp [Pi.single_apply, hpq]; ring_nf; rw [Complex.I_sq]; ring
    · by_cases hi' : i = q
      · subst hi'; simp [Pi.single_apply, hi]; ring_nf; rw [Complex.I_sq]; ring
      · simp [Pi.single_apply, hi, hi']
  set α : ℂ := (1 / 2 : ℂ) * (I.s ⟨0, h⟩ + n - 1) + (-(Complex.I / 2)) * γ with hα
  set β : ℂ := (-(1 / 2) : ℂ) * (I.s ⟨0, h⟩ + n - 1) + (-(Complex.I / 2)) * γ with hβ
  have hdp : ∀ v : Y, ℓ' (E' p p v) = α * ℓ' v := fun v => by
    rw [hE'v, hDp, hsplitA _ _ _ _ v hH₀ hTc, hℓH _ (v : kFinVec ε I.ρ).2, hℓT _ (v : kFinVec ε I.ρ).2, hℓ'v, hα]
    ring
  have hdq : ∀ v : Y, ℓ' (E' q q v) = β * ℓ' v := fun v => by
    rw [hE'v, hDq, hsplitA _ _ _ _ v hH₀ hTc, hℓH _ (v : kFinVec ε I.ρ).2, hℓT _ (v : kFinVec ε I.ρ).2, hℓ'v, hβ]
    ring
  obtain ⟨i, k, hik, hi, hk⟩ := GlobalTheory.T.highest_weight_functional_character Y n E' χ hGl' hqdet p q hpq ℓ' α β hℓ'0 hoffp hoffq hdp hdq
  exact ⟨i, k, hik, by rw [hi, hk, hα, hβ]; ring⟩

end GlobalTheory.IndCap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegratedOperatorNormalizedIndicatorProdFixed
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem integralOp_normInd_fix : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, IsOpen (K' v : Set (GLoc D.sp.cm.sig V.gram v))) → (∀ v, K' v ≤ Kv V v) → (∀ᶠ v in cofinite, K' v = Kv V v) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W), (∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x) → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)))) P → P x = x := by
  intro D V μf hH h1 ν hν K' hO hle hcof W _ _ σ x hx P hP
  set c : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
    fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) with hc
  have hcpt : ∀ v, IsCompact (K' v : Set (GLoc D.sp.cm.sig V.gram v)) := fun v =>
    (isCompact_stabLoc _ _ (frameLat V) v).of_isClosed_subset ((K' v).isClosed_of_isOpen (hO v)) (hle v)
  have hpos : ∀ v, (μf v).real (K' v : Set (GLoc D.sp.cm.sig V.gram v)) ≠ 0 := fun v => by
    have := hH v
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(hO v).measure_ne_zero (μf v) ⟨1, (K' v).one_mem⟩, (hcpt v).measure_lt_top.ne⟩
  have hint : ∀ v, ∫ y, c v y ∂μf v = 1 := fun v => by
    simp only [hc, normInd, Pi.smul_apply]
    rw [integral_smul]
    erw [integral_indicator_const (μ := μf v) (1 : ℂ) (hO v).measurableSet]
    simp only [Complex.real_smul, smul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (hpos v))
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) c := by
    refine ⟨fun v => Submodule.smul_mem _ _ (indicator_mem_SB (hO v) (hcpt v)), ?_⟩
    filter_upwards [hcof, h1] with v hv hv1
    simp only [hc, normInd, unitLoc, hv]
    simp [Measure.real, hv1]
  have hI : ∫ g, finFn V c g ∂ν = 1 := by
    rw [hν.2 c hfam]
    simp [hint]
  have hsupp : ∀ g : GfC V, finFn V c g ≠ 0 → ∀ v, finLoc V v g ∈ K' v := by
    intro g hg v
    have hfin : (Function.mulSupport fun v => c v (proj D.sp.cm.sig V.gram v (g : GA D V))).Finite :=
      Filter.eventually_cofinite.1 ((hfam.2.and (eventually_proj_mem_stabLoc _ _ (frameLat V) (g : GA D V))).mono
        fun v hv => by show c v _ = 1; rw [hv.1, unitLoc, indicator_of_mem hv.2, Pi.one_apply])
    by_contra hv
    apply hg
    refine finprod_eq_zero _ v ?_ hfin
    change normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) (finLoc V v g) = 0
    simp [normInd, Set.indicator_of_notMem hv]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  have e : (fun g => finFn V c g * l (σ g x)) = fun g => finFn V c g * l x := by
    funext g
    by_cases h : finFn V c g = 0
    · simp [h]
    · rw [hx g (hsupp g h)]
  rw [map_sub, (hP x l).2, e, integral_mul_const, hI, one_mul, sub_self]

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsParabolicIsotropicFlagStabilizerSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SplitFlag.isParabRad_parAt : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (𝔉 : IsoFlag V), GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.IsParabRad (parAt 𝔉 s)
      ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) := by
  intro D V v s 𝔉
  obtain ⟨d, hd, g₀, hg₀⟩ := GlobalTheory.T.exists_gl_adaptedBasis_monotoneSubspaceChain (GlobalTheory.SplitFlag.flagChain 𝔉 s.emb) (GlobalTheory.SplitFlag.flagChain_mono _ _)
    (GlobalTheory.SplitFlag.flagChain_zero _ _) (GlobalTheory.SplitFlag.flagChain_last _ _ s.cm)
  obtain ⟨hP, hN⟩ := GlobalTheory.T.translated_standard_chain_stabilizer_radical _ d hd g₀ hg₀
  have key : ∀ x : GL (Fin V.rank) (Fv D.host.F v),
      splitHom D.sp.cm.sig V.gram s.emb (s.equiv.symm x) = s.basis * x * s.basis⁻¹ := fun x =>
    splitHom_splitEquivIn_symm s.cm s.herm s.emb s.basis x
  have hmap : ∀ (H : Subgroup (GLoc D.sp.cm.sig V.gram v)) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ H.map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v)) ↔ s.equiv.symm x ∈ H :=
    fun H x => ⟨by rintro ⟨g, hg, rfl⟩; simpa using hg, fun hx => ⟨_, hx, s.equiv.apply_symm_apply x⟩⟩
  have hconj : ∀ (H : Subgroup (GL (Fin V.rank) (Fv D.host.F v))) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy (s.basis⁻¹ * g₀) H ↔ s.basis * x * s.basis⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g₀ H := by
    intro H x
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  refine ⟨2 * 𝔉.k + 1, d, hd, s.basis⁻¹ * g₀, ?_, ?_⟩
  · ext x
    rw [parAt, hmap, GlobalTheory.T.mem_isotropicFlagParabolic_iff_splitPlaceChain D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hP]
  · ext x
    rw [hmap, GlobalTheory.T.mem_isotropic_flag_unipotent_iff_split_chain_trivial D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hN]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZeroStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularSemisimple_of_testFunction_ne_zero : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (δ : GF V) (x : GA D V), tensor D.sp.cm.sig V.gram fa ff (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 := by
  first | exact @GlobalTheory.RegSupp.isRegSS_of_tensor_ne_zero | exact GlobalTheory.RegSupp.isRegSS_of_tensor_ne_zero | (intros; apply GlobalTheory.RegSupp.isRegSS_of_tensor_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinCuspApprox

variable {D : D7}

abbrev avgN (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e φ

def KStab (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (s : Set D.what₂.Tau) (W : Submodule ℂ (GA D N.V → ℂ)) : Prop :=
  ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), N.M.fr τ * g * (N.M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (N.M.ε τ) →
    ∀ f ∈ W, rTr N.V (atTau θ N.V τ g) f ∈ W

theorem kStab_empty (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (W : Submodule ℂ (GA D N.V → ℂ)) : KStab θ N ∅ W := fun _ h => h.elim

end GlobalTheory.KFinCuspApprox

end
end

