import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAtStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  first | exact @GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | exact GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | (intros; apply GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAtStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  first | exact @GlobalTheory.NabStab.polyAction_mem_locP_nabStd | exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd | (intros; apply GlobalTheory.NabStab.polyAction_mem_locP_nabStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.Minor

open ReciprocityTheory.ChartRestriction.G Matrix

abbrev Incr (a d : ℕ) : Type := {s : Fin a → Fin d // StrictMono s}

noncomputable def toIncr {a d : ℕ} (S : Set.powersetCard (Fin d) a) : Incr a d :=
  ⟨GlobalTheory.subsetEnum S, (S.1.orderEmbOfFin S.2).strictMono⟩

theorem toIncr_bijective {a d : ℕ} : Function.Bijective (toIncr (a := a) (d := d)) := by
  constructor
  · intro S S' h
    have h1 : GlobalTheory.subsetEnum S = GlobalTheory.subsetEnum S' := congrArg Subtype.val h
    have h2 : (S.1 : Set (Fin d)) = S'.1 := by
      rw [← GlobalTheory.range_subsetEnum S, ← GlobalTheory.range_subsetEnum S', h1]
    exact Subtype.ext (Finset.coe_injective h2)
  · intro s
    have hc : (Finset.univ.image s.1).card = a := by
      rw [Finset.card_image_of_injective _ s.2.injective]; simp
    refine ⟨⟨Finset.univ.image s.1, hc⟩, Subtype.ext ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) s.2).symm

theorem det_submatrix_mul {R l o : Type*} [CommRing R] {a d : ℕ}
    (A : Matrix l (Fin d) R) (B : Matrix (Fin d) o R) (r : Fin a → l) (c : Fin a → o) :
    ((A * B).submatrix r c).det = ∑ s : Incr a d, (A.submatrix r s.1).det * (B.submatrix s.1 c).det := by
  rw [GlobalTheory.det_submatrix_mul_eq_sum_minors]
  exact Fintype.sum_bijective toIncr toIncr_bijective _ _ fun S => rfl

theorem det_submatrix_one {a d : ℕ} (s s' : Incr a d) :
    ((1 : Matrix (Fin d) (Fin d) ℂ).submatrix s.1 s'.1).det = if s = s' then 1 else 0 := by
  obtain ⟨I, rfl⟩ := toIncr_bijective.2 s
  obtain ⟨J, rfl⟩ := toIncr_bijective.2 s'
  split_ifs with h
  · rw [← h, submatrix_one _ (toIncr I).2.injective, det_one]
  · have h' : I ≠ J := fun e => h (by rw [e])
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h'
    have h1 : x ∈ Set.range (GlobalTheory.subsetEnum I) := by rw [GlobalTheory.range_subsetEnum]; exact hxI
    have h2 : x ∉ Set.range (GlobalTheory.subsetEnum J) := by rw [GlobalTheory.range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩

theorem minors_orth {a d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (s' s'' : Incr a d) :
    ∑ s : Incr a d, (u.submatrix s'.1 s.1).det * star (u.submatrix s''.1 s.1).det = if s' = s'' then 1 else 0 := by
  rw [← det_submatrix_one, ← (Matrix.mem_unitaryGroup_iff.1 hu), det_submatrix_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← det_conjTranspose, conjTranspose_submatrix, star_eq_conjTranspose]

theorem sum_norm_sq_eq {ι : Type*} [Fintype ι] (K : ι → ι → ℂ)
    (hK : ∀ i j, ∑ t, K i t * star (K j t) = if i = j then 1 else 0) (v : ι → ℂ) :
    ∑ t, ‖∑ i, K i t * v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_sum, h, star_sum, star_mul', Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ j, ∑ t, K i t * v i * (star (K j t) * star (v j)) = (if i = j then 1 else 0) * (v i * star (v j)) := by
    intro j
    rw [← hK, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem prod_prod_sum {R T S : Type*} [CommSemiring R] [Fintype T] [DecidableEq T] [Fintype S] (n : T → ℕ)
    (f : ∀ τ, Fin (n τ) → S → R) :
    ∏ τ, ∏ j, ∑ s, f τ j s = ∑ t : ∀ τ, Fin (n τ) → S, ∏ τ, ∏ j, f τ j (t τ j) := by
  simp only [Fintype.prod_sum]

theorem polyDeriv_subst {σ κ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [Fintype κ] {F : W → ℂ}
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • MvPolynomial.monomial 0 1 := by
      simp [MvPolynomial.smul_eq_C_mul]
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, h]
    simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
      -MvPolynomial.monomial_zero']
  | add P Q hP hQ => simp only [map_add, I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, hΦ, Finset.mul_sum, I2.jof_polyDeriv_sum, GlobalTheory.ThFr.polyDeriv_mul_X hF, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, MvPolynomial.C_mul', I2.polyDeriv_smul, GlobalTheory.ThFr.polyDeriv_mul_X hF, funext hP]
    simp

variable {D : D7} {a d : ℕ}

theorem applyAt0_eq (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) (G : VC D a d → ℂ) :
    GL3Theta.applyAt0 D P G = I2.polyDeriv P (coordV D) G 0 := by
  unfold GL3Theta.applyAt0 I2.polyDeriv taylor
  refine Finset.sum_congr rfl fun α _ => ?_
  have h : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [mul_assoc, mul_div_cancel₀ _ h]
  rfl

theorem applyAt0_comp {κ : Type} [Fintype κ] {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (A : VC D a d →ₗ[ℂ] VC D a d) (s : GL3Theta.Idx D a d → κ → ℂ) (j : GL3Theta.Idx D a d → κ → GL3Theta.Idx D a d)
    (hA : ∀ l, A (coordV D l) = ∑ k, s l k • coordV D (j l k)) (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D P (fun z => G (A z)) = GL3Theta.applyAt0 D
      (MvPolynomial.aeval (fun l => ∑ k, MvPolynomial.C (s l k) * (MvPolynomial.X (j l k) : MvPolynomial _ ℂ)) P) G := by
  have hG' : ContDiff ℂ (⊤ : ℕ∞) G := contDiff_infty.2 fun k => I2.contDiff_of_differentiable_fd hG k
  rw [applyAt0_eq, applyAt0_eq, polyDeriv_subst hG' s j _ (fun l => MvPolynomial.aeval_X _ l)]
  have h := GlobalTheory.Jet.polyDeriv_comp_clm P (coordV D) hG (LinearMap.toContinuousLinearMap A) 0
  rw [map_zero] at h
  refine h.trans ?_
  congr 1
  funext l
  exact hA l

def mulR (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, z τ i k * u τ k j
  map_add' x y := by
    funext τ i j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_assoc]

def mulL (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, u τ i k * z τ k j
  map_add' x y := by
    funext τ i j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_left_comm]

theorem mulR_coordV (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (l : GL3Theta.Idx D a d) :
    mulR u (coordV D l) = ∑ k, u l.1 l.2.2 k • coordV D (l.1, l.2.1, k) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : i' = i <;>
    simp [mulR, coordV, Finset.sum_apply, h1, h2]

theorem mulL_coordV (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (l : GL3Theta.Idx D a d) :
    mulL u (coordV D l) = ∑ k, u l.1 k l.2.1 • coordV D (l.1, k, l.2.2) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : j' = j <;>
    simp [mulL, coordV, Finset.sum_apply, h1, h2]

theorem applyAt0_minorPol_mulR {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulR u z)) =
      (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G := by
  rw [applyAt0_comp hG (mulR u) (fun l k => u l.1 l.2.2 k) (fun l k => (l.1, l.2.1, k)) (mulR_coordV u),
    applyAt0_eq, applyAt0_eq, ← I2.polyDeriv_smul]
  congr 1
  unfold minorPol
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_pow, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [AlgHom.map_det, RingHom.map_det, mul_comm, ← det_transpose (RingHom.mapMatrix _ _), ← det_mul]
  congr 1
  ext1 i i'
  simp [Matrix.mul_apply, mul_comm]

theorem applyAt0_minorPol_mulL {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulL u z)) =
      ∑ t' : Tup D a d n, (∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) *
        GL3Theta.applyAt0 D (minorPol D t') G := by
  rw [applyAt0_comp hG (mulL u) (fun l k => u l.1 k l.2.1) (fun l k => (l.1, k, l.2.2)) (mulL_coordV u)]
  simp only [applyAt0_eq, ← I2.polyDeriv_smul]
  rw [← I2.jof_polyDeriv_sum]
  congr 1
  unfold minorPol
  simp only [MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  rw [← prod_prod_sum n (fun τ j (s : Incr a d) => MvPolynomial.C ((u τ).submatrix s.1 (t τ j).1).det *
    (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s.1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det)]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  have h := det_submatrix_mul ((u τ)ᵀ.map (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (Matrix.of fun (i : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (t τ j).1 id
  rw [AlgHom.map_det]
  refine Eq.trans ?_ (h.trans (Finset.sum_congr rfl fun s _ => ?_))
  · congr 1
    ext1 i i'
    simp [Matrix.mul_apply]
  · rw [RingHom.map_det, ← det_transpose (RingHom.mapMatrix _ _)]
    rfl

end GlobalTheory.NormSum.Minor

open GlobalTheory.NormSum.Minor ReciprocityTheory.ChartRestriction.G in

theorem GlobalTheory.NormSum.applyAt0_minorPol_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  intro D a d n G hG
  refine ⟨fun u t => applyAt0_minorPol_mulR hG u t, fun u hu => ?_, fun c P => ?_, fun G' P hG' => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (sum_norm_sq_eq
      (fun t' t : Tup D a d n => ∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) (fun t' t'' => ?_) _)
    · rw [← applyAt0_minorPol_mulL hG u t]
      rfl
    · simp only [star_prod, ← Finset.prod_mul_distrib]
      rw [← prod_prod_sum n (fun τ j (s : Incr a d) => ((u τ).submatrix (t' τ j).1 s.1).det *
        star ((u τ).submatrix (t'' τ j).1 s.1).det)]
      simp only [fun τ => minors_orth (a := a) (hu τ)]
      split_ifs with h
      · simp [h]
      · obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hτ
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  · rw [applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_smul_fun P _ hG]
  · rw [applyAt0_eq, applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_add_fun P _ hG hG']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AreaBoundedOfDiscrEqOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators UpperHalfPlane Real

namespace GlobalTheory.LatticeAreaBound

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ}
    (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} fun w : ℂ => (w ^ (2 * k))⁻¹
  have h2 := tsum_subtype (L.lattice : Set ℂ) fun w : ℂ => (w ^ (2 * k))⁻¹
  simp only [eisG, PeriodPair.G, one_div]
  refine h1.trans (Eq.trans (tsum_congr fun w => ?_) h2.symm)
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    TaylorLogMetric.discr Λ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_G L Λ h (by norm_num), eisG_eq_G L Λ h (by norm_num)]
  rfl

theorem area_eq {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have hA : 0 < ‖a‖ ^ 2 * τ.im := by positivity
  have key : ∀ m n m' n' : ℤ,
      ((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im
        = ((n * m' - m * n' : ℤ) : ℝ) * (‖a‖ ^ 2 * τ.im) := fun m n m' n' => by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  refine IsLeast.csInf_eq ⟨⟨hA, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩, ?_⟩
  · rw [key, abs_of_nonneg (by simpa using hA.le)]
    simp
  · rintro b ⟨hb, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h₁
    obtain ⟨m', n', rfl⟩ := (h _).1 h₂
    rw [key, abs_mul, abs_of_pos hA] at hb ⊢
    have h0 : n * m' - m * n' ≠ 0 := fun e => by simp [e] at hb
    have h1 : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_left hA.le h1

theorem exists_bound_discriminant :
    ∃ C : ℝ, ∀ τ : ℍ, τ.im ^ 6 * ‖ModularForm.discriminant τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound CuspForm.discriminant
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  have hy := τ.im_pos
  rw [CuspForm.coe_discriminant, show (((12 : ℤ) : ℝ) / 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, le_div_iff₀ (by positivity)] at h
  rwa [mul_comm]

theorem area_bounded_of_discr_eq_one : ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → 0 < area Λ ∧ area Λ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_discriminant
  refine ⟨max 1 ((2 * π) ^ 12 * C), lt_max_of_lt_left one_pos, ?_⟩
  rintro Λ ⟨w₁, w₂, hi, rfl⟩ hd
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ L.lattice := fun z => by
    rw [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  rw [area_eq ha fun x => (hL x).trans (h x)]
  rw [discr_eq L _ hL, ← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h] at hd
  have e := congrArg norm hd
  rw [norm_mul, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le],
    norm_one, div_pow, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)] at e
  have hb : (‖a‖ ^ 2 * τ.im) ^ 6 ≤ (2 * π) ^ 12 * C := by
    calc (‖a‖ ^ 2 * τ.im) ^ 6 = ‖a‖ ^ 12 * τ.im ^ 6 := by ring
      _ = (2 * π) ^ 12 * (τ.im ^ 6 * ‖ModularForm.discriminant τ‖) := by rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC τ) (by positivity)
  refine ⟨by positivity, ?_⟩
  rcases le_total (‖a‖ ^ 2 * τ.im) 1 with h1 | h1
  · exact le_max_of_le_left h1
  · exact le_max_of_le_right ((le_self_pow₀ h1 (by norm_num)).trans hb)

end GlobalTheory.LatticeAreaBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.AdelicApprox

variable (D : D7)

theorem levelC_natCast (n : ℕ) : Formalism.UG.P.levelafC D.host.E (n : 𝓞 ℚ) = (n : AE D) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]

theorem exists_denom (x : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * x ∈ OhE D := by
  obtain ⟨d, hd, hx⟩ := Formalism.UG.P.levelaf_denom x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hd
  · rw [← levelC_natCast, ← hc, Formalism.UG.P.levelafC_mul, mul_assoc]
    exact mul_mem (Formalism.UG.P.levelafC_mem c) hx

theorem exists_approx (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ r : D.host.E, ∃ w ∈ OhE D, s = inc D r + (n : AE D) * w := by
  rw [← levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨_, t, ht, h⟩

theorem one_mem_inverse_halfDifferent : (1 : D.host.E) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hne : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hspec : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) =
      D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  rw [hspec] at hne
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; rintro h; exact hne (by rw [h]; simp)
  rw [FractionalIdeal.mem_coe]
  unfold Host.AA0
  rw [FractionalIdeal.mem_inv_iff hB]
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy

theorem mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) (t : AE D)
    (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  unfold IhE at ht
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, a, ha, u, hu, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * u, mul_mem hs hu, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem absNorm_mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) :
    (Ideal.absNorm cc : AE D) * s ∈ IhE D cc := by
  refine AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, 1, one_mem_inverse_halfDifferent D, s, hs, ?_⟩
  simp

theorem approx_mod_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ →
    (∀ (y : AE D) (m : ℕ), 0 < m → ∃ e : D.host.E, ∃ t ∈ IhE D cc,
      inc D e - y = (m : AE D) * t) ∧
    (∀ y : AE D, ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D) ∧
    (∀ s ∈ OhE D, ∀ t ∈ IhE D cc, s * t ∈ IhE D cc) := by
  intro D cc hcc
  refine ⟨fun y m hm => ?_, exists_denom D, mul_mem_IhE D cc⟩
  obtain ⟨k, hk, hy⟩ := exists_denom D y
  have hn : 0 < Ideal.absNorm cc :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨r, w, hw, h⟩ := exists_approx D (k * m * Ideal.absNorm cc)
    (Nat.mul_pos (Nat.mul_pos hk hm) hn) _ hy
  refine ⟨(k : D.host.E)⁻¹ * r, _, absNorm_mul_mem_IhE D cc (-w) (neg_mem hw), ?_⟩
  have hu : inc D (k : D.host.E)⁻¹ * (k : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  rw [map_mul]
  push_cast at h
  linear_combination (-inc D (k : D.host.E)⁻¹) * h +
    (y - (m : AE D) * (Ideal.absNorm cc : AE D) * w) * hu

end GlobalTheory.AdelicApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualFrLatticeHolds
section
namespace GlobalTheory

theorem dualFrLattice_holds : Formalism.L2.DIV.DualFrLattice :=
  GlobalTheory.DualLat.dualFr_lattice_and_hdual.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_isLattice_and_hermitianDual : DualFrLattice ∧ DualFrHdual := by
  first | exact @GlobalTheory.DualLat.dualFr_lattice_and_hdual | exact GlobalTheory.DualLat.dualFr_lattice_and_hdual | (intros; apply GlobalTheory.DualLat.dualFr_lattice_and_hdual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfAbsNormEqSq
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QuadPlaces

theorem conjSrc_one {M : Type} [Field M] [NumberField M] (w : HeightOneSpectrum (𝓞 M)) :
    GlobalTheory.CuspRep.conjSrc (1 : M ≃+* M) w = w := by
  refine (GlobalTheory.CuspRep.eq_conjSrc ?_).symm
  rw [GlobalTheory.Mem.Chr.conjPl_iff_comap]
  ext x
  rfl

theorem eq_of_absNorm_eq_sq {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (h2 : Module.finrank K M = 2) (w w' : HeightOneSpectrum (𝓞 M))
    (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2)
    (hw' : w'.under (𝓞 K) = w.under (𝓞 K)) : w' = w := by
  set v := w.under (𝓞 K) with hv
  have : v.asIdeal.IsPrime := v.isPrime
  have : w.asIdeal.IsPrime := w.isPrime
  have hl : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  have hpow := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  have hf : w.asIdeal.inertiaDeg (𝓞 K) = 2 :=
    Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) (hpow.trans hN)
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) (M ≃ₐ[K] M)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (M ≃ₐ[K] M), hf, IsGalois.card_aut_eq_finrank, h2,
    ← mul_assoc] at hfund
  have h1 : (v.asIdeal.primesOver (𝓞 M)).ncard * v.asIdeal.ramificationIdxIn (𝓞 M) = 1 := by omega
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.1 (Nat.eq_one_of_mul_eq_one_right h1)
  have a : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨w.isPrime, hl⟩
  have b : w'.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨w'.isPrime, hl'⟩
  rw [hP, Set.mem_singleton_iff] at a b
  exact HeightOneSpectrum.ext (b.trans a.symm)

theorem main : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], Module.finrank K M = 2 → ∀ (s : M ≃ₐ[K] M), s ≠ 1 → ∀ w : HeightOneSpectrum (𝓞 M), (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w ∨ w' = GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) ∧ (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w).under (𝓞 K) = w.under (𝓞 K) ∧ GlobalTheory.CuspRep.conjSrc ((1 : M ≃ₐ[K] M) : M ≃+* M) w = w ∧ (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 → GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w = w) := by
  intro K M _ _ _ _ _ _ h2 s hs w
  have hu : GlobalTheory.Mem.Chr.ConjPl s.toRingEquiv (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) w :=
    GlobalTheory.CuspRep.conjPl_conjSrc (s : M ≃+* M) w
  have hunder : (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w).under (𝓞 K) = w.under (𝓞 K) :=
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl s h2 hs (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) w).2 (Or.inr hu)).symm
  refine ⟨fun w' hw' => ?_, hunder, conjSrc_one w, fun hN => eq_of_absNorm_eq_sq h2 w _ hN hunder⟩
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl s h2 hs (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) w').1
      (hw'.trans hunder.symm) with h | h
  · exact Or.inr h
  · exact Or.inl ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ _).unique h hu)

end GlobalTheory.QuadPlaces
end

