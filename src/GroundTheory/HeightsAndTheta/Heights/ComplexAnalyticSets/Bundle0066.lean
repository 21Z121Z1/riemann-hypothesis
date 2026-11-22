import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsClosedComplexSubmanifoldIn
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenFixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix Metric

noncomputable section

namespace IsolatedFibreOpenOfGeneric

theorem isClosed_zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroLocus J) := by
  have h : zeroLocus J = ⋂ q ∈ J, {x | eval x q = 0} := by
    ext x
    simp [zeroLocus]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem eval_linPoly {n k : ℕ} (B : Matrix (Fin k) (Fin n) ℂ) (z : Fin n → ℂ) (i : Fin k) :
    eval z (linPoly B.mulVecLin i) = (B *ᵥ z) i := by
  simp [linPoly, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem finiteProjection_near (hGen : GenericProjectionFinite.Statement) {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsAffVariety J k) (A : Matrix (Fin k) (Fin n) ℂ) :
    ∃ M : Matrix (Fin k) (Fin n) ℂ,
      ∀ᶠ t in 𝓝[≠] (0 : ℂ), IsFiniteProjection J (A + t • (M - A)).mulVecLin := by
  obtain ⟨⟨S, ⟨M, f, hfS, hf⟩, hS⟩, -⟩ := hGen n k J hJ.isPrime hJ.dim
  refine ⟨M, ?_⟩
  set a : Fin k × Fin n → ℂ := fun p => A p.1 p.2
  set b : Fin k × Fin n → ℂ := fun p => (M - A) p.1 p.2
  have hg : ∀ t : ℂ, eval (fun p : Fin k × Fin n => (A + t • (M - A)) p.1 p.2) f = eval (a + t • b) f :=
    fun t => rfl
  have han : ∀ t : ℂ, AnalyticAt ℂ (fun t : ℂ => eval (a + t • b) f) t := fun t =>
    (AnalyticOnNhd.eval_mvPolynomial f _ trivial).comp
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  rcases (han 0).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hz := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (fun t _ => han t)
      isPreconnected_univ (Set.mem_univ 0) h0 (Set.mem_univ 1)
    apply hf
    have h1 : (fun p : Fin k × Fin n => M p.1 p.2) = a + (1 : ℂ) • b := by
      funext p
      simp [a, b]
    rw [h1]
    exact hz
  · filter_upwards [hne] with t ht
    exact hS _ ⟨f, hfS, by rw [hg]; exact ht⟩

theorem proof (hGen : GenericProjectionFinite.Statement) (hFin : FiniteMapOpen.Statement) :
    IsolatedFibreOpen.Statement := by
  intro n k J A x hJ hx ⟨W, hW, hiso⟩ W' hW'
  have hZc : IsClosed (zeroLocus J) := isClosed_zeroLocus J
  have hAc : ∀ B : Matrix (Fin k) (Fin n) ℂ, Continuous fun z : Fin n → ℂ => B *ᵥ z :=
    fun B => continuous_const.matrix_mulVec continuous_id

  obtain ⟨r0, hr0, hr0W⟩ := Metric.mem_nhds_iff.1 (inter_mem hW hW')
  have hr : 0 < r0 / 2 := half_pos hr0
  have hcb : closedBall x (r0 / 2) ⊆ W ∩ W' :=
    (closedBall_subset_ball (half_lt_self hr0)).trans hr0W
  have hSc : IsCompact (zeroLocus J ∩ closedBall x (r0 / 2)) :=
    (isCompact_closedBall x _).inter_left hZc
  have hKc : IsCompact (zeroLocus J ∩ sphere x (r0 / 2)) := (isCompact_sphere x _).inter_left hZc

  have hAK : A *ᵥ x ∉ (fun z => A *ᵥ z) '' (zeroLocus J ∩ sphere x (r0 / 2)) := by
    rintro ⟨z, ⟨hzZ, hzs⟩, hzA⟩
    have hzx : z = x := hiso z (hcb (sphere_subset_closedBall hzs)).1 hzZ hzA
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 ((hKc.image (hAc A)).isClosed.isOpen_compl) _ hAK
  obtain ⟨M, hM⟩ := finiteProjection_near hGen hJ A
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hAc (M - A)).continuousOn
  have hAt : ∀ (t : ℂ) (z : Fin n → ℂ), (A + t • (M - A)) *ᵥ z = A *ᵥ z + t • ((M - A) *ᵥ z) :=
    fun t z => by rw [add_mulVec, smul_mulVec]
  have hclose : ∀ t : ℂ, ‖t‖ * C < ε / 4 → ∀ z ∈ zeroLocus J ∩ closedBall x (r0 / 2),
      dist ((A + t • (M - A)) *ᵥ z) (A *ᵥ z) < ε / 4 := by
    intro t ht z hz
    rw [dist_eq_norm, hAt, add_sub_cancel_left, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg t)).trans_lt ht

  have hstep : ∀ t : ℂ, IsFiniteProjection J (A + t • (M - A)).mulVecLin → ‖t‖ * C < ε / 4 →
      ball (A *ᵥ x) (ε / 4) ⊆
        (fun z => (A + t • (M - A)) *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) := by
    intro t hfin ht
    set B := A + t • (M - A) with hB
    have hcomp : (Ideal.Quotient.mkₐ ℂ J).comp (aeval fun i => linPoly B.mulVecLin i) =
        projAlgHom J B.mulVecLin := by
      rw [MvPolynomial.comp_aeval]
      rfl
    have hTo : IsOpen ((fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2))) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨z, ⟨hzZ, hzb⟩, rfl⟩
      have h := hFin n k J (fun i => linPoly B.mulVecLin i) hJ.isPrime (by rw [hcomp]; exact hfin.1)
        (by rw [hcomp]; exact hfin.2) z hzZ (ball x (r0 / 2)) (isOpen_ball.mem_nhds hzb)
      simpa only [eval_linPoly] using h
    have hTS : (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) ⊆
        (fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) :=
      Set.image_mono (Set.inter_subset_inter_right _ ball_subset_closedBall)
    have hSim : IsClosed ((fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2))) :=
      (hSc.image (hAc B)).isClosed
    have hxS : x ∈ zeroLocus J ∩ closedBall x (r0 / 2) := ⟨hx, mem_closedBall_self hr.le⟩
    have hsub : ball (A *ᵥ x) (ε / 2) ⊆ (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) := by
      refine (convex_ball _ _).isPreconnected.subset_of_closure_inter_subset hTo ?_ ?_
      · refine ⟨B *ᵥ x, ?_, x, ⟨hx, mem_ball_self hr⟩, rfl⟩
        rw [mem_ball]
        linarith [hclose t ht x hxS]
      · rintro _ ⟨hcl, hball⟩
        obtain ⟨z, hzS, rfl⟩ := closure_minimal hTS hSim hcl
        refine ⟨z, ⟨hzS.1, ?_⟩, rfl⟩
        by_contra hzb
        have hzs : z ∈ sphere x (r0 / 2) :=
          mem_sphere.2 (le_antisymm (mem_closedBall.1 hzS.2) (not_lt.1 (by simpa [mem_ball] using hzb)))
        apply hεK (show A *ᵥ z ∈ ball (A *ᵥ x) ε from ?_) ⟨z, ⟨hzS.1, hzs⟩, rfl⟩
        rw [mem_ball] at hball ⊢
        have h1 := hclose t ht z hzS
        rw [dist_comm] at h1
        linarith [dist_triangle (A *ᵥ z) (B *ᵥ z) (A *ᵥ x)]
    exact (ball_subset_ball (by linarith)).trans (hsub.trans hTS)

  have h0 : Tendsto (fun t : ℂ => ‖t‖ * C) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℂ => ‖t‖ * C := continuous_norm.mul continuous_const
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
    simpa using h
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ * C < ε / 4 := h0.eventually (gt_mem_nhds (by positivity))
  refine mem_of_superset (ball_mem_nhds (A *ᵥ x) (by positivity : (0 : ℝ) < ε / 4)) ?_
  intro y hy
  have hz : ∀ t : ℂ, ∃ z : Fin n → ℂ,
      (∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y) →
        z ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ z = y := by
    intro t
    by_cases h : ∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose zf hzf using hz
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      zf t ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ zf t = y := by
    filter_upwards [hM, hsmall] with t h1 h2
    exact hzf t (hstep t h1 h2 hy)
  obtain ⟨a, haS, hacl⟩ := hSc (f := map zf (𝓝[≠] (0 : ℂ)))
    (le_principal_iff.2 (hev.mono fun t ht => ht.1))
  have hlim : Tendsto (fun t => A *ᵥ zf t) (𝓝[≠] (0 : ℂ)) (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [hev] with t ht
    rw [← ht.2, hAt, sub_add_cancel_left, norm_neg, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ht.1) (norm_nonneg _)
  have hay : A *ᵥ a = y :=
    eq_of_nhds_neBot (hacl.map (hAc A).continuousAt (tendsto_map'_iff.2 hlim))
  exact ⟨a, ⟨haS.1, (hcb haS.2).2⟩, hay⟩

end IsolatedFibreOpenOfGeneric

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology Filter Matrix ComplexSets

noncomputable section

namespace IsolatedFibreOpenPoly

variable {n d : ℕ}

def graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + d)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.append X p)

def graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + d)) ℂ) :=
  P.comap (graphSubst p)

def graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + d) → ℂ :=
  Fin.append x fun i => eval x (p i)

def firstPart (z : Fin (n + d) → ℂ) : Fin n → ℂ :=
  fun j => z (Fin.castAdd d j)

def lastRows (n d : ℕ) : Matrix (Fin d) (Fin (n + d)) ℂ :=
  fun i j => if j = Fin.natAdd n i then 1 else 0

theorem lastRows_mulVec (z : Fin (n + d) → ℂ) : lastRows n d *ᵥ z = fun i => z (Fin.natAdd n i) := by
  funext i
  simp [lastRows, Matrix.mulVec, dotProduct, ite_mul]

theorem firstPart_graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    firstPart (graphPt p x) = x := by
  funext j
  simp [firstPart, graphPt, Fin.append_left]

theorem graphPt_natAdd (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin d) :
    graphPt p x (Fin.natAdd n i) = eval x (p i) := by
  simp [graphPt, Fin.append_right]

theorem continuous_firstPart : Continuous (firstPart : (Fin (n + d) → ℂ) → Fin n → ℂ) :=
  continuous_pi fun _ => continuous_apply _

theorem eval_graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + d)) ℂ) : eval x (graphSubst p q) = eval (graphPt p x) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [graphSubst]
  | add q r hq hr => simp only [map_add, hq, hr]
  | mul_X q i hq =>
    simp only [map_mul, graphSubst, aeval_X, eval_X]
    congr 1
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [graphPt, Fin.append_left]
    · simp [graphPt, Fin.append_right]

theorem graphSubst_rename (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    graphSubst p (rename (Fin.castAdd d) q) = q := by
  rw [graphSubst, aeval_rename]
  have h : (Fin.append X p ∘ Fin.castAdd d : Fin n → MvPolynomial (Fin n) ℂ) = X := by
    funext j
    simp [Fin.append_left]
  rw [h, aeval_X_left_apply]

theorem graphSubst_surjective (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Function.Surjective (graphSubst p) :=
  fun q => ⟨rename (Fin.castAdd d) q, graphSubst_rename p q⟩

theorem isPrime_graphIdeal {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.IsPrime)
    (p : Fin d → MvPolynomial (Fin n) ℂ) : (graphIdeal P p).IsPrime := by
  have := hP
  unfold graphIdeal
  infer_instance

theorem ringKrullDim_graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + d)) ℂ ⧸ graphIdeal P p) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set f : MvPolynomial (Fin (n + d)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mk P).comp (graphSubst p).toRingHom with hf
  have hsurj : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (graphSubst_surjective p)
  have hker : graphIdeal P p = RingHom.ker f := by
    rw [hf, ← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj))

theorem graphPt_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin d → MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ zeroSet P) : graphPt p x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) := by
  intro q hq
  rw [← eval_graphSubst]
  exact hx _ hq

theorem firstPart_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    firstPart z ∈ zeroSet P := by
  intro q hq
  have h := hz (rename (Fin.castAdd d) q) (by
    show graphSubst p (rename (Fin.castAdd d) q) ∈ P
    rw [graphSubst_rename]
    exact hq)
  rw [eval_rename] at h
  exact h

theorem natAdd_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) (i : Fin d) :
    z (Fin.natAdd n i) = eval (firstPart z) (p i) := by
  have h := hz (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) (by
    show graphSubst p (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) ∈ P
    rw [map_sub, graphSubst_rename, graphSubst, aeval_X, Fin.append_right, sub_self]
    exact P.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  exact h

theorem eq_graphPt_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    z = graphPt p (firstPart z) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · simp [graphPt, firstPart, Fin.append_left]
  · rw [natAdd_of_mem hz i, graphPt_natAdd]

theorem proof (hOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement) : IsolatedFibreOpenPoly.Statement := by
  intro n d P p x hP hdim hx ⟨W, hW, hiso⟩ W' hW'
  have hV : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety (graphIdeal P p) d :=
    ⟨isPrime_graphIdeal hP p, by rw [ringKrullDim_graphIdeal]; exact hdim⟩
  have hAx : lastRows n d *ᵥ graphPt p x = fun i => eval x (p i) := by
    rw [lastRows_mulVec]
    funext i
    exact graphPt_natAdd p x i
  have hN : ∀ U ∈ 𝓝 x, firstPart ⁻¹' U ∈ 𝓝 (graphPt p x) := fun U hU =>
    continuous_firstPart.continuousAt.preimage_mem_nhds (by rw [firstPart_graphPt]; exact hU)
  have hisoG : ∀ z ∈ firstPart ⁻¹' W, z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) →
      lastRows n d *ᵥ z = lastRows n d *ᵥ graphPt p x → z = graphPt p x := by
    intro z hzW hz hAz
    have hfz : firstPart z = x := by
      refine hiso _ ⟨firstPart_mem hz, hzW⟩ fun i => ?_
      have h := congrFun hAz i
      rw [lastRows_mulVec, lastRows_mulVec] at h
      simp only at h
      rw [natAdd_of_mem hz, graphPt_natAdd] at h
      exact h
    rw [eq_graphPt_of_mem hz, hfz]
  have h := hOpen (n + d) d (graphIdeal P p) (lastRows n d) (graphPt p x) hV (graphPt_mem p hx)
    ⟨firstPart ⁻¹' W, hN W hW, hisoG⟩ (firstPart ⁻¹' W') (hN W' hW')
  rw [hAx] at h
  refine Filter.mem_of_superset h ?_
  rintro _ ⟨z, ⟨hz, hzW'⟩, rfl⟩
  refine ⟨firstPart z, ⟨firstPart_mem hz, hzW'⟩, ?_⟩
  show (fun i => eval (firstPart z) (p i)) = lastRows n d *ᵥ z
  rw [lastRows_mulVec]
  funext i
  exact (natAdd_of_mem hz i).symm

end IsolatedFibreOpenPoly

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isClosed_zeroSetIn_of_ideal {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (zeroSetIn I) := by
  have h : zeroSetIn I = ⋂ q ∈ I, {z : σ → ℂ | eval z q = 0} := by
    ext z; simp [zeroSetIn]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem HolomorphicOnSubset.continuousWithinAt_trace {σ : Type*} [Fintype σ] {g : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S) {z : σ → ℂ} (hz : z ∈ S) :
    ContinuousWithinAt g S z := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg z hz
  have hFc : ContinuousAt F z := (hF.differentiableAt (hV.mem_nhds hzV)).continuousAt
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hgF ⟨hz, hzV⟩)
  filter_upwards [inter_mem_nhdsWithin S (hV.mem_nhds hzV)] with x hx using hgF hx

theorem HolomorphicOnSubset.differentiableAt_comp {σ : Type*} [Fintype σ] {k : ℕ}
    {g : (σ → ℂ) → ℂ} {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S)
    {s : (Fin k → ℂ) → σ → ℂ} {y : Fin k → ℂ} (hs : DifferentiableAt ℂ s y)
    (hS : ∀ᶠ y' in 𝓝 y, s y' ∈ S) : DifferentiableAt ℂ (fun y' => g (s y')) y := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg (s y) hS.self_of_nhds
  have hFd : DifferentiableAt ℂ F (s y) := hF.differentiableAt (hV.mem_nhds hzV)
  have hev : ∀ᶠ y' in 𝓝 y, s y' ∈ V := hs.continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  refine (hFd.comp y hs).congr_of_eventuallyEq ?_
  filter_upwards [hS, hev] with y' h1 h2 using hgF ⟨h1, h2⟩

theorem LocalTrace.proof (hbc : LocalBranchedCovering.Statement) : LocalTrace.Statement := by
  intro σ _ I w U g hI hw hU hg
  obtain ⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, hwonly, hprop, hδd, hδne, hsheets,
    hopen⟩ := hbc σ I w U hI hw hU
  have hZc : IsClosed (zeroSetIn I) := isClosed_zeroSetIn_of_ideal I
  have hKc : IsCompact (zeroSetIn I ∩ closure W) := hWc.inter_left hZc
  have hgc : ContinuousOn g (zeroSetIn I ∩ U) := fun z hz => hg.continuousWithinAt_trace hz
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ zeroSetIn I ∩ closure W, ‖g z‖ ≤ M :=
    hKc.exists_bound_of_continuousOn (hgc.mono (Set.inter_subset_inter_right _ hWU))

  obtain ⟨f, hf⟩ : ∃ f : (Fin k → ℂ) → ℂ,
      ∀ y, f y = ∑ᶠ z ∈ {z | z ∈ zeroSetIn I ∩ W ∧ A z = y}, g z := ⟨_, fun _ => rfl⟩
  have hfsum : ∀ (s : Fin m → σ → ℂ) (y : Fin k → ℂ),
      (∀ j, s j ∈ zeroSetIn I ∩ W ∧ A (s j) = y) → Function.Injective s →
      (∀ z ∈ zeroSetIn I ∩ W, A z = y → z ∈ Set.range s) → f y = ∑ j, g (s j) := by
    intro s y hs hinj hcov
    have hset : {z | z ∈ zeroSetIn I ∩ W ∧ A z = y} = Set.range s := by
      ext z
      constructor
      · rintro ⟨hz, hAz⟩
        exact hcov z hz hAz
      · rintro ⟨j, rfl⟩
        exact hs j
    rw [hf, hset, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  have hmemU : ∀ z ∈ zeroSetIn I ∩ W, z ∈ zeroSetIn I ∩ U := fun z hz =>
    ⟨hz.1, hWU (subset_closure hz.2)⟩
  have hfd : DifferentiableOn ℂ f (D ∩ {t | δ t ≠ 0}) := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    have hev : f =ᶠ[𝓝 y] fun y' => ∑ j, g (s j y') := by
      filter_upwards [hOo.mem_nhds hyO] with y' hy'
      exact hfsum (fun j => s j y') y' (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun j _ => ?_
    refine hg.differentiableAt_comp ((hsd j).differentiableAt (hOo.mem_nhds hyO)) ?_
    filter_upwards [hOo.mem_nhds hyO] with y' hy' using hmemU _ ((hsO y' hy').1 j).1
  have hfb : ∀ y ∈ D ∩ {t | δ t ≠ 0}, ‖f y‖ ≤ m * M := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    rw [hfsum (fun j => s j y) y (hsO y hyO).1 (hsO y hyO).2.1 (hsO y hyO).2.2]
    calc ‖∑ j, g (s j y)‖ ≤ ∑ j : Fin m, ‖g (s j y)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum fun j _ =>
          hM _ ⟨((hsO y hyO).1 j).1.1, subset_closure ((hsO y hyO).1 j).1.2⟩
      _ = m * M := by simp
  obtain ⟨T, hTd, hTf⟩ := RiemannExtensionAnalytic.proof k D δ f hDo hδd hδne hfd (fun τ _ =>
    ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨m * M, by
      rintro _ ⟨y, ⟨⟨_, hyD⟩, hyδ⟩, rfl⟩
      exact hfb y ⟨hyD, hyδ⟩⟩⟩)
  refine ⟨k, A, W ∩ A ⁻¹' D, D, m, T, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩,
    fun z hz => hWU (subset_closure hz.1), hDo, hAwD,
    fun z hz hAz => hwonly z ⟨hz.1, hz.2.1⟩ hAz, hTd, ?_⟩
  intro y hyD

  have hseq : ∀ n : ℕ, ∃ t ∈ D ∩ Metric.ball y (1 / ((n : ℝ) + 1)), δ t ≠ 0 := fun n =>
    hδne _ (hDo.inter Metric.isOpen_ball) Set.inter_subset_left
      ⟨y, hyD, Metric.mem_ball_self (by positivity)⟩
  choose t ht htδ using hseq
  have htD : ∀ n, t n ∈ D := fun n => (ht n).1
  have httend : Tendsto t atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (ht n).2)
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hX : ∀ n, ∃ X : Fin m → σ → ℂ, (∀ j, X j ∈ zeroSetIn I ∩ W ∧ A (X j) = t n) ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = t n → z ∈ Set.range X) ∧ T (t n) = ∑ j, g (X j) := by
    intro n
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets (t n) (htD n) (htδ n)
    obtain ⟨h1, h2, h3⟩ := hsO (t n) hyO
    exact ⟨fun j => s j (t n), h1, h3, by rw [hTf ⟨htD n, htδ n⟩, hfsum _ (t n) h1 h2 h3]⟩
  choose X hXmem hXcov hXT using hX

  have hKm : IsCompact (Set.univ.pi fun _ : Fin m => zeroSetIn I ∩ closure W) :=
    isCompact_univ_pi fun _ => hKc
  obtain ⟨x, hxK, φ, hφ, hXφ⟩ := hKm.tendsto_subseq (x := X) (fun n => Set.mem_univ_pi.2 fun j =>
    ⟨(hXmem n j).1.1, subset_closure (hXmem n j).1.2⟩)
  have hxK' : ∀ j, x j ∈ zeroSetIn I ∩ closure W := fun j => Set.mem_univ_pi.1 hxK j
  have hxj : ∀ j, Tendsto (fun n => X (φ n) j) atTop (𝓝 (x j)) := fun j => tendsto_pi_nhds.1 hXφ j
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 y) := httend.comp hφ.tendsto_atTop
  have hAx : ∀ j, A (x j) = y := fun j =>
    tendsto_nhds_unique ((A.continuous.tendsto _).comp (hxj j))
      (Tendsto.congr (fun n => ((hXmem (φ n) j).2).symm) htφ)
  have hxW : ∀ j, x j ∈ W := fun j => hprop (x j) (hxK' j) (by rw [hAx j]; exact hyD)
  have hT1 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (T y)) :=
    (hTd.differentiableAt (hDo.mem_nhds hyD)).continuousAt.tendsto.comp htφ
  have hT2 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (∑ j, g (x j))) := by
    have hs : Tendsto (fun n => ∑ j, g (X (φ n) j)) atTop (𝓝 (∑ j, g (x j))) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      exact (hgc (x j) ⟨(hxK' j).1, hWU (hxK' j).2⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hxj j, Filter.Eventually.of_forall fun n =>
          hmemU _ (hXmem (φ n) j).1⟩)
    exact Tendsto.congr (fun n => (hXT (φ n)).symm) hs
  refine ⟨x, fun j => ⟨⟨(hxK' j).1, hxW j, by show A (x j) ∈ D; rw [hAx j]; exact hyD⟩, hAx j⟩,
    ?_, tendsto_nhds_unique hT1 hT2⟩

  rintro z ⟨hzZ, hzW, -⟩ hAz
  by_contra hz
  have hne : ∀ j, 0 < dist z (x j) := fun j => dist_pos.2 fun h => hz ⟨j, h.symm⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo z hzW
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ r ∧ ∀ j, 2 * ε < dist z (x j) := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε) (Filter.Eventually.and (nhdsWithin_le_nhds (Iic_mem_nhds hr) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ r)
      (Filter.eventually_all.2 fun j => nhdsWithin_le_nhds ?_))
    have h2 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
    exact h2.eventually (gt_mem_nhds (hne j))
  obtain ⟨ε, hε0, hεr, hεd⟩ := hε.exists
  have hnbhd := hopen z ⟨hzZ, hzW⟩ ε hε0
  rw [hAz] at hnbhd
  have hev1 : ∀ᶠ n in atTop, t (φ n) ∈ A '' (zeroSetIn I ∩ Metric.ball z ε) := htφ hnbhd
  have hev2 : ∀ᶠ n in atTop, ∀ j, dist (X (φ n) j) (x j) < ε :=
    Filter.eventually_all.2 fun j => Metric.tendsto_nhds.1 (hxj j) ε hε0
  obtain ⟨n, ⟨z', ⟨hz'Z, hz'b⟩, hAz'⟩, hd⟩ := (hev1.and hev2).exists
  have hz'W : z' ∈ W := hrW (Metric.ball_subset_ball hεr hz'b)
  obtain ⟨j, hj⟩ := hXcov (φ n) z' ⟨hz'Z, hz'W⟩ hAz'
  have h1 := hd j
  rw [hj] at h1
  rw [Metric.mem_ball] at hz'b
  have h3 := dist_triangle z z' (x j)
  have h4 := hεd j
  rw [dist_comm] at hz'b
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCutHess
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.AnForm

noncomputable section

def LogLogCutHess.Statement : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ), ∃ a b : ℝ,
    |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
    hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
    hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y

end

end GroundTheory.Heights₂.Heights
end

