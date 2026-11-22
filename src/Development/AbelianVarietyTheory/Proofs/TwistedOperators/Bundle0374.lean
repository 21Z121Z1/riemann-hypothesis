import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0355
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIntertwiner
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CuspIntertwiner

theorem exists_extend {ι H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (e : ι → H) (f : ι → K)
    (he : Dense (Submodule.span ℂ (Set.range e) : Set H)) (c : ℂ) (h : ∀ i j, ⟪f i, f j⟫_ℂ = c * ⟪e i, e j⟫_ℂ) :
    ∃ A : H →L[ℂ] K, ∀ i, A (e i) = f i := by
  have hd : DenseRange (Finsupp.linearCombination ℂ e) := by
    rw [← Finsupp.range_linearCombination] at he
    exact he
  have hn : ∀ x : ι →₀ ℂ, ‖Finsupp.linearCombination ℂ f x‖ ≤ √‖c‖ * ‖Finsupp.linearCombination ℂ e x‖ := by
    intro x
    have h1 : ⟪Finsupp.linearCombination ℂ f x, Finsupp.linearCombination ℂ f x⟫_ℂ =
        c * ⟪Finsupp.linearCombination ℂ e x, Finsupp.linearCombination ℂ e x⟫_ℂ := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
        inner_smul_right, h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 := congrArg norm h1
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at h2
    refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_)
    rw [h2, mul_pow, Real.sq_sqrt (norm_nonneg _)]
  refine ⟨(Finsupp.linearCombination ℂ f).extendOfNorm (Finsupp.linearCombination ℂ e), fun i => ?_⟩
  have := LinearMap.extendOfNorm_eq hd ⟨_, hn⟩ (Finsupp.single i 1)
  simpa using this

theorem continuous_tens {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) : Continuous t := by
  refine continuous_iff_continuousAt.2 fun y => tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h1 : Continuous fun x => ‖t x - t y‖ := by
    simp only [@norm_eq_sqrt_re_inner ℂ, inner_sub_sub_self, h]
    fun_prop
  simpa using h1.tendsto y

theorem dense_span_tens {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hd : Dense (Submodule.span ℂ (Set.range t) : Set H))
    {ι : Type} (s : ι → ∀ v, E v) (hs : DenseRange s) :
    Dense (Submodule.span ℂ (Set.range fun i => t (s i)) : Set H) := by
  have h1 : Submodule.span ℂ (Set.range t) ≤ (Submodule.span ℂ (Set.range fun i => t (s i))).topologicalClosure := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    refine map_mem_closure (continuous_tens t h) (hs x) ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact dense_closure.1 (hd.mono h1)

theorem eq_of_inner_eq {X H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : X → H)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set H)) {p q : H} (h : ∀ z, ⟪t z, p⟫_ℂ = ⟪t z, q⟫_ℂ) : p = q := by
  have h0 : innerSL ℂ (p - q) = 0 := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨z, rfl⟩
    rw [innerSL_apply_apply, ContinuousLinearMap.zero_apply, ← inner_conj_symm, inner_sub_right, h z, sub_self,
      map_zero]
  have := congrArg (fun L : H →L[ℂ] ℂ => L (p - q)) h0
  simp only [innerSL_apply_apply, ContinuousLinearMap.zero_apply, inner_self_eq_zero] at this
  exact sub_eq_zero.1 this

theorem inner_update {κ H : Type} [Fintype κ] [DecidableEq κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (z x : ∀ v, E v) (i : κ) (a : E i) :
    ⟪t z, t (Function.update x i a)⟫_ℂ = ⟪z i, a⟫_ℂ * ∏ v ∈ Finset.univ.erase i, ⟪z v, x v⟫_ℂ := by
  rw [h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

def tensML {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hd : Dense (Submodule.span ℂ (Set.range t) : Set H)) :
    ContinuousMultilinearMap ℂ E H where
  toFun := t
  map_update_add' x i a b := by
    refine (eq_of_inner_eq t hd fun z => ?_)
    rw [inner_add_right, inner_update t h, inner_update t h, inner_update t h, inner_add_right, add_mul]
  map_update_smul' x i c a := by
    refine (eq_of_inner_eq t hd fun z => ?_)
    rw [inner_smul_right, inner_update t h, inner_update t h, inner_smul_right, mul_assoc]
  cont := continuous_tens t h

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem denseRange_vec (M : DSModel V S) : DenseRange fun (u : M.Vec) (τ : D.what₂.Tau) => (u τ : M.H τ) := by
  refine (dense_pi Set.univ fun τ _ => Formalism.IndefR.SchurOrthogonalityAlt.sm_dense M τ).mono fun x hx => ?_
  exact ⟨fun τ => ⟨x τ, hx τ trivial⟩, rfl⟩

theorem coe_update [DecidableEq D.what₂.Tau] (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun τ' => ((Function.update u τ w τ' : M.sm τ') : M.H τ')) =
      Function.update (fun τ' => (u τ' : M.H τ')) τ (w : M.H τ) := by
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

set_option maxHeartbeats 1000000 in

theorem exists_of_isMultMap (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {T : MMap M}
    (hT : IsMultMap θ M ∅ (fun _ => 1) T) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧
      ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  classical
  have h𝓕 := isFundamentalDomain_stdDom (GQ V) μ
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := θ) (M := M) (J := ∅) (χ := fun _ => 1) hP μ (stdDom (GQ V))
    hθ inferInstance h𝓕 T (Submodule.subset_span hT) T (Submodule.subset_span hT)
  have hm : ∀ u, MemL2Quotient (GQ V) μ (T u) := by
    intro u
    refine (memL2_iff_fundamental_domain h𝓕).2 ⟨(hT.aut u).left, ?_⟩
    refine (memLp_two_iff_integrable_sq_norm (hT.aut u).cont.measurable.aestronglyMeasurable).2
      ((hc u u).1.norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨F, hFl, hF⟩ : ∃ F : M.Vec → DividedPowerChartLift V μ, (∀ u, lift (GQ V) (F u) =ᵐ[μ] T u) ∧
      ∀ u u', ⟪F u, F u'⟫_ℂ = c * ∏ τ, ⟪(u τ : M.H τ), (u' τ : M.H τ)⟫_ℂ := by
    refine ⟨fun u => (hm u).toL2, fun u => (hm u).lift_toL2_ae_eq, fun u u' => ?_⟩
    rw [← (hc u u').2, MemL2Quotient.inner_toL2_eq_theta_pairing (hm u') (hm u), pet_eq h𝓕 (hT.aut u').left (hT.aut u).left]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [RCLike.star_def]
    ring
  obtain ⟨K, _, _, t0, ht0⟩ := GlobalTheory.HilbTensorExists.exists_pre M.H
  obtain ⟨L, _, _, _, s, hs, hd⟩ := GlobalTheory.HilbTensorExists.exists_complete_dense t0
  have hs' : ∀ x y, ⟪s x, s y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ := fun x y => (hs x y).trans (ht0 x y)
  have hvec := denseRange_vec M
  have hdense := dense_span_tens s hs' hd _ hvec
  have hG : ∀ u u' : M.Vec, ⟪F u, F u'⟫_ℂ = c * ⟪s (fun τ => (u τ : M.H τ)), s (fun τ => (u' τ : M.H τ))⟫_ℂ := fun u u' => by
    rw [hF, hs']
  obtain ⟨A, hA⟩ := exists_extend (ι := M.Vec) (fun u => s fun τ => (u τ : M.H τ)) F hdense c hG
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), ∀ u : M.Vec, Φ (fun τ => (u τ : M.H τ)) = F u :=
    ⟨A.compContinuousMultilinearMap (tensML s hs' hd), hA⟩
  refine ⟨Φ, (mem_homDS hθ).2 ⟨fun y => ?_, fun τ g hg y => ?_⟩, fun u => ?_⟩
  · refine hvec.induction_on y ((Submodule.isClosed_topologicalClosure _).preimage Φ.cont) fun u => ?_
    show Φ _ ∈ GlobalTheory.Cusp.L2cusp V μ
    rw [hΦ u]
    exact GlobalTheory.Cusp.mem_L2cusp_of_ae_eq ⟨(hT.aut u).cont, (hT.aut u).left, hT.cusp u⟩ (hFl u)
  · have h1 : Continuous fun y : (∀ τ, M.H τ) => Φ (Function.update y τ (M.rep τ g (y τ))) :=
      Φ.cont.comp (continuous_id.update τ ((M.rep τ g).continuous.comp (continuous_apply τ)))
    have h2 : Continuous fun y : (∀ τ, M.H τ) => RG V μ (atTau θ V τ g) (Φ y) :=
      (RG V μ (atTau θ V τ g)).continuous.comp Φ.cont
    refine congrFun (hvec.equalizer h1 h2 (funext fun u => ?_)) y
    let w : M.sm τ := ⟨M.rep τ g (u τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ g hg _ (u τ).2⟩
    have e1 := hT.equiv τ g hg u w rfl
    have e2 : Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ g (u τ)) =
        fun τ' => ((Function.update u τ w τ' : M.sm τ') : M.H τ') := (coe_update u τ w).symm
    show Φ (Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ g (u τ))) =
      RG V μ (atTau θ V τ g) (Φ fun τ' => (u τ' : M.H τ'))
    rw [e2, hΦ (Function.update u τ w), hΦ u]
    refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
    refine (hFl _).trans ?_
    rw [e1]
    refine (EventuallyEq.trans ?_ (lift_R _ _).symm)
    exact ((measurePreserving_mul_right μ (atTau θ V τ g)).quasiMeasurePreserving.ae (hFl u)).mono
      fun x hx => hx.symm
  · rw [hΦ u]
    exact hFl u

theorem eq_of_represents {μ : Measure (GA D V)} [μ.IsHaarMeasure] {T : MMap M}
    {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)}
    (h : ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v)
    (h' : ∀ v : M.Vec, lift (GQ V) (Φ' fun τ => (v τ : M.H τ)) =ᵐ[μ] T v) : Φ = Φ' := by
  refine ContinuousMultilinearMap.ext fun y => congrFun ((denseRange_vec M).equalizer Φ.cont Φ'.cont
    (funext fun v => ?_)) y
  exact l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((h v).trans (h' v).symm)

theorem exists_of_mem (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {T : MMap M}
    (hT : T ∈ GlobalTheory.CuspMult.allMaps θ M) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧
      ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact exists_of_isMultMap hP hθ μ hT
  | zero =>
    refine ⟨0, zero_mem _, fun v => ?_⟩
    simp only [ContinuousMultilinearMap.zero_apply, MultilinearMap.zero_apply]
    exact ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)
  | add T T' _ _ ih ih' =>
    obtain ⟨Φ, h1, h2⟩ := ih
    obtain ⟨Φ', h1', h2'⟩ := ih'
    refine ⟨Φ + Φ', add_mem h1 h1', fun v => ?_⟩
    simp only [ContinuousMultilinearMap.add_apply, MultilinearMap.add_apply]
    exact Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add _ _)) ((h2 v).add (h2' v))
  | smul a T _ ih =>
    obtain ⟨Φ, h1, h2⟩ := ih
    refine ⟨a • Φ, Submodule.smul_mem _ a h1, fun v => ?_⟩
    simp only [ContinuousMultilinearMap.smul_apply, MultilinearMap.smul_apply]
    exact Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul a _)) ((h2 v).const_smul a)

theorem existsUnique_intertwiner : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ T ∈ GlobalTheory.CuspMult.allMaps θ M, ∃! Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  intro hP D θ hθ V S M μ _ _ T hT
  obtain ⟨Φ, h1, h2⟩ := exists_of_mem hP hθ μ hT
  exact ⟨Φ, ⟨h1, h2⟩, fun Φ' h' => eq_of_represents h'.2 h2⟩

end GlobalTheory.CuspIntertwiner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InvTransposeIso

def ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) : GL n A →* GL m A where
  toFun g := ⟨((g⁻¹).1ᵀ).submatrix e.symm e.symm, (g.1ᵀ).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.submatrix_one_equiv]⟩
  map_one' := Units.ext (by ext i j; simp [Matrix.one_apply])
  map_mul' g h := Units.ext (by
    show (((g * h)⁻¹).1ᵀ).submatrix e.symm e.symm =
      ((g⁻¹).1ᵀ).submatrix e.symm e.symm * ((h⁻¹).1ᵀ).submatrix e.symm e.symm
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, ← Units.val_mul, _root_.mul_inv_rev])

theorem ctr_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : (ctr e g).1 = ((g⁻¹).1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_inv_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ((ctr e g)⁻¹).1 = (g.1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ctr e.symm (ctr e g) = g :=
  Units.ext (by rw [ctr_val, ctr_inv_val]; ext i j; simp)

theorem key_rel {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (c : A →+* A)
    {H Hi K : Matrix n n A} (hHi : H * Hi = 1) (hK : Hi = -Kᵀ) (g : GL n A)
    (hg : (g.1.map c)ᵀ * H * g.1 = H) :
    (((g⁻¹).1ᵀ).map c)ᵀ * K * (g⁻¹).1ᵀ = K := by
  have hHiH : Hi * H = 1 := mul_eq_one_comm.1 hHi
  have h1 : g.1.map c * (g⁻¹).1.map c = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hY : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H = 1 := by
    calc (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H
        = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * ((g.1.map c)ᵀ * H * g.1) := by rw [hg]
      _ = (g⁻¹).1 * Hi * (g.1.map c * (g⁻¹).1.map c)ᵀ * H * g.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc _ Hi H, hHiH, Matrix.mul_one,
            Units.inv_mul]
  have hY' : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ = Hi := by
    calc _ = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * (H * Hi) := by rw [hHi, Matrix.mul_one]
      _ = Hi := by rw [← Matrix.mul_assoc, hY, Matrix.one_mul]
  have hKt : Kᵀ = -Hi := by rw [hK, neg_neg]
  apply Matrix.transpose_injective
  rw [Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hKt, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hY']

theorem reindex_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {J : Matrix m m A} {M : Matrix n n A}
    (h : (M.map c)ᵀ * J.submatrix e e * M = J.submatrix e e) :
    ((M.submatrix e.symm e.symm).map c)ᵀ * J * M.submatrix e.symm e.symm = J := by
  have hJ : J = (J.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
  have hM : ((M.submatrix e.symm e.symm).map c)ᵀ = ((M.map c)ᵀ).submatrix e.symm e.symm := rfl
  rw [hM]
  conv_lhs => rw [hJ]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h, ← hJ]

theorem ctr_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {H Hi : Matrix n n A} {J : Matrix m m A} (hHi : H * Hi = 1)
    (hK : Hi = -(Jᵀ.submatrix e e)) (g : GL n A) (hg : Formalism.UG.cT c g.1 * H * g.1 = H) :
    Formalism.UG.cT c (ctr e g).1 * J * (ctr e g).1 = J :=
  reindex_rel c e (key_rel c hHi hK g hg)

theorem inv_rel {K : Type} [Field K] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n K) (B : Matrix m m K) (e : n ≃ m) (h : A⁻¹ = -(Bᵀ.submatrix e e)) (hA : IsUnit A.det) :
    B⁻¹ = -(Aᵀ.submatrix e.symm e.symm) := by
  have h1 : A * -(Bᵀ.submatrix e e) = 1 := by rw [← h]; exact Matrix.mul_nonsing_inv A hA
  have h2 : -(B.submatrix e e) * Aᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_submatrix, Matrix.transpose_transpose,
      Matrix.transpose_one] at this
    exact this
  have h3 : Aᵀ * -(B.submatrix e e) = 1 := mul_eq_one_comm.1 h2
  have h4 : Aᵀ.submatrix e.symm e.symm * -B = 1 := by
    calc Aᵀ.submatrix e.symm e.symm * -B
        = Aᵀ.submatrix e.symm e.symm * (-(B.submatrix e e)).submatrix e.symm e.symm := by
          congr 1; ext i j; simp
      _ = (Aᵀ * -(B.submatrix e e)).submatrix e.symm e.symm := Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [h3, Matrix.submatrix_one_equiv]
  exact Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, ← Matrix.mul_neg]; exact h4)

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

theorem gram_inv_rel {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    W.gram⁻¹ = -(V.gramᵀ.submatrix e.symm e.symm) :=
  inv_rel V.gram W.gram e h (Formalism.L2.Theta.gram_det_ne V).isUnit

theorem mem_HR {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : ctr e (matHom V g) ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  have hHi : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK : (V.gram⁻¹).map (incA D) = -(((W.gram.map (incA D))ᵀ).submatrix e e) := by
    rw [h]; ext i j; simp
  exact ctr_rel (cA D) e hHi hK (matHom V g) g.2

theorem mem_UJ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (r : GL (Fin V.rank) D.host.E) (hr : r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    ctr e r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  exact ctr_rel _ e (Matrix.mul_nonsing_inv _ hdet) h r hr

def fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V →* GA D W where
  toFun g := (⟨ctr e (matHom V g), mem_HR e h g⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram)
  map_one' := Subtype.ext (by simp only [map_one]; rfl)
  map_mul' g g' := Subtype.ext (by simp only [map_mul]; rfl)

theorem mt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : Formalism.L2.Theta.mt W (fwd e h g) = ((Formalism.L2.Theta.mt V g⁻¹)ᵀ).submatrix e.symm e.symm := by
  show (ctr e (matHom V g)).1 = _
  rw [ctr_val, ← map_inv]; rfl

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

def iso {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V ≃* GA D W :=
  { fwd e h with
    invFun := fwd e.symm (gram_inv_rel e h)
    left_inv := fun g => Subtype.ext (ctr_ctr e g.1)
    right_inv := fun g => Subtype.ext (ctr_ctr e.symm g.1) }

theorem continuous_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    Continuous (fwd e h) := by
  have hv : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : GA D V => ((matHom V g)⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun g : GA D V => (((matHom V g)⁻¹).1ᵀ).submatrix e.symm e.symm
    exact hi.matrix_transpose.matrix_submatrix _ _
  · show Continuous fun g : GA D V => ((matHom V g).1ᵀ).submatrix e.symm e.symm
    exact hv.matrix_transpose.matrix_submatrix _ _

theorem fwd_GQ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (γ : GA D V) (hγ : γ ∈ GQ V) : fwd e h γ ∈ GQ W := by
  obtain ⟨r, hr, hrγ⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈
    HFin (AF D.host.F) D.sp.cm.sig V.gram)
  refine Subgroup.mem_subgroupOf.2 ⟨ctr e r, mem_UJ e h r hr, ?_⟩
  show Formalism.UG.bc (inclR (AF D.host.F)) (ctr e r) = ctr e γ.1
  rw [← hrγ]
  exact Units.ext (by ext i j; rfl)

theorem suppAt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (a : AE D) (g : GA D V) (hg : SuppAt a V g) : SuppAt a W (fwd e h g) := by
  have hYG : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hsub : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, hYG, Matrix.mul_one, neg_sub]
  intro i j
  have hij : (Formalism.L2.Theta.mt W (fwd e h g) - 1) i j = (Formalism.L2.Theta.mt V g⁻¹ - 1) (e.symm j) (e.symm i) := by
    rw [mt_fwd]
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply,
      e.symm.injective.eq_iff, eq_comm]
  rw [hij, hsub, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k (e.symm i)]

theorem det_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).det = (Formalism.L2.Theta.mt V g⁻¹).det := by
  rw [mt_fwd, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

theorem sub_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).submatrix e e = (Formalism.L2.Theta.mt V g⁻¹)ᵀ := by
  rw [mt_fwd]; ext i j; simp

theorem grp_contra : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  intro D T S' e₂ h
  exact ⟨iso e₂ h, continuous_fwd e₂ h, fun γ hγ => fwd_GQ e₂ h γ hγ, sub_fwd e₂ h,
    fun a g hg => suppAt_fwd e₂ h a g hg, det_fwd e₂ h⟩

end GlobalTheory.InvTransposeIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.FinFockLin

theorem finF_lin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X),
  IsFinF ψ θ ε A B 0 ∧ (∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g)) ∧
  (∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f)) ∧
  (∀ f g P, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g →
    fockF ψ θ ε A B (f + g) P = fockF ψ θ ε A B f P + fockF ψ θ ε A B g P) ∧
  ∀ (c : ℂ) f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B (c • f) P = c • fockF ψ θ ε A B f P := by
  intro D ψ θ hψ hθ ε M X A B
  have hsm : ∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f) := by
    intro c f hf
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c hf.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z c hf.1, hf.2 τ z, smul_zero]
  have hadd : ∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g) := by
    intro f g hf hg
    refine ⟨GlobalTheory.OrientedHeis.theta_add hf.1 hg.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_add hψ hθ τ _ z hf.1 hg.1, hf.2 τ z, hg.2 τ z, add_zero]
  have h0 : IsFinF ψ θ ε A B 0 := by
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, fun τ z => ?_⟩
    have h := GlobalTheory.FockIndep.annih_smul hψ hθ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) z 0
      (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε M) (T := X))
    simpa only [zero_smul] using h
  refine ⟨h0, hadd, hsm, fun f g P hf hg => ?_, fun c f P hf => ?_⟩
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb 1 hf.1 hg.1 P
    rw [one_smul, one_smul] at h
    exact h
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb c hf.1
      h0.1 P
    rw [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ _ _ hψ hθ, add_zero] at h
    exact h

end GlobalTheory.FinFockLin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow : RowModels → RowStep → RowTower := by
  first | exact @GlobalTheory.SepRows.rowTower_of_step | exact GlobalTheory.SepRows.rowTower_of_step | (intros; apply GlobalTheory.SepRows.rowTower_of_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianReadingDifferentiableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockGaussianReading_differentiable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ x, Differentiable ℂ (rd ψ σ A B f x) := by
  first | exact @GlobalTheory.FockEntire.rd_differentiable | exact GlobalTheory.FockEntire.rd_differentiable | (intros; apply GlobalTheory.FockEntire.rd_differentiable <;> assumption)
end

