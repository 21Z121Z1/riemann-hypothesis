import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorPlaceNorm
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm

open Formalism.BasicNotions Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n n' : ℕ}

def placeNorm (lam : DomWeight n) (f : nablaSq ℂ n lam) : ℝ :=
  Real.sqrt (normFock lam f.1 f.1).re

def coefNorm (lam : ι → DomWeight n) (F : VV ℂ lam) : ℝ :=
  Real.sqrt (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) F F).re

def pureTen (lam : ι → DomWeight n) (f : ∀ τ, nablaSq ℂ n (lam τ)) : VV ℂ lam :=
  ⟨ten fun τ => (f τ).1, Submodule.subset_span ⟨fun τ => (f τ).1, fun τ => (f τ).2, rfl⟩⟩

def IsTensorMap (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') : Prop :=
  ∀ f : ∀ τ, nablaSq ℂ n (lam τ), T (pureTen lam f) = pureTen lam' fun τ => A τ (f τ)

def TensorNormBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (c : ι → ℝ),
    (∀ τ, 0 ≤ c τ) →
    (∀ τ (f : nablaSq ℂ n (lam τ)), placeNorm (lam' τ) (A τ f) ≤ c τ * placeNorm (lam τ) f) →
    (∃! T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap lam lam' A T) ∧
      ∀ T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap lam lam' A T →
        ∀ F : VV ℂ lam, coefNorm lam' (T F) ≤ (∏ τ, c τ) * coefNorm lam F

theorem fockF_eq_fockS {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = fockS f f := by
  unfold Formalism.REAL.fockF fockS mfact
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem fockS_self_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : ∃ r : ℝ, 0 ≤ r ∧ fockS f f = r := by
  refine ⟨∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ), by positivity, ?_⟩
  unfold fockS
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Complex.conj_mul']
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceSubstitution
section
open MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceSubstitution

open Formalism.GradedWeylDivisibility Formalism.L2.DIV

def substTr {r r' : ℕ} (n : ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    MvPolynomial (Fin r × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin r' × Fin n) ℂ :=
  aeval fun v => ∑ b : Fin r', C (x b v.1) * X (b, v.2)

def substTrO {r r' : ℕ} (n : ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    MvPolynomial (Option (Fin r × Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Option (Fin r' × Fin n)) ℂ :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r', C (x b v.1) * X (some (b, v.2)))

theorem substTr_mem {r r' n : ℕ} (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ)
    {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n ν) : substTr n x f ∈ dualWeyl ℂ r' n ν := by
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  refine ⟨isWH_algHom (substTr n x) (colW r n) (colW r' n) (fun v => ?_) hf.1, ?_⟩
  · rw [substTr, aeval_X]
    exact IsWeightedHomogeneous.sum _ _ _ fun b _ => (isWeightedHomogeneous_X ℂ _ (b, v.2)).C_mul _
  · intro l j hlj
    have h1 : (colAddGen ℂ l j).comp (substTr n x) = (substTrO n x).comp (colAddGen ℂ l j) := by
      apply MvPolynomial.algHom_ext
      intro v
      by_cases h : v.2 = j
      · simp [substTr, colAddGen, substTrO, h, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
      · simp [substTr, colAddGen, substTrO, h]
    have h2 : (rename (R := ℂ) (some : Fin r' × Fin n → Option (Fin r' × Fin n))).comp (substTr n x) =
        (substTrO n x).comp (rename some) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [substTr, substTrO]
    have e1 := DFunLike.congr_fun h1 f
    have e2 := DFunLike.congr_fun h2 f
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, e2, hf.2 l j hlj]

def rhoNu {r r' n : ℕ} (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    dualWeyl ℂ r n ν →ₗ[ℂ] dualWeyl ℂ r' n ν :=
  (substTr n x).toLinearMap.restrict fun _ hf => substTr_mem ν x hf

def invNorm {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : dualWeyl ℂ r n ν) : ℝ :=
  √((fockS f.1 f.1).re / (fockS (hw ℂ hn ν) (hw ℂ hn ν)).re)

def IsOpNorm {r r' n : ℕ} (hn : n ≤ r) (hn' : n ≤ r') (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ) (c : ℝ) :
    Prop :=
  IsLeast {t : ℝ | 0 ≤ t ∧ ∀ f : dualWeyl ℂ r n ν, invNorm hn' ν (rhoNu ν x f) ≤ t * invNorm hn ν f} c

def singVal {n r' : ℕ} (x : Matrix (Fin r') (Fin n) ℂ) (i : Fin n) : ℝ :=
  (Matrix.toEuclideanLin x : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin r')).singularValues i.val

def PolyFunctorOpNorm : Prop :=
  ∀ (n₀ n₁ : ℕ) (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ), Antitone ν → ∀ x : Matrix (Fin n₁) (Fin n₀) ℂ,
    IsOpNorm le_rfl h ν x (∏ i, singVal x i ^ ν i) ∧
    IsOpNorm le_rfl h ν (x.map (starRingEnd ℂ)) (∏ i, singVal x i ^ ν i)

theorem substTr_mul {r r' r'' n : ℕ} (x' : Matrix (Fin r'') (Fin r') ℂ) (x : Matrix (Fin r') (Fin r) ℂ) :
    substTr n (x' * x) = (substTr n x').comp (substTr n x) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [substTr, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply, algebraMap_eq,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem substTr_vec {r r' n : ℕ} (x : Matrix (Fin r') (Fin r) ℂ) (v : Fin r → ℂ) (s : Fin n) :
    substTr n x (∑ a, C (v a) * X (a, s)) = ∑ b, C ((x *ᵥ v) b) * X (b, s) := by
  simp only [substTr, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem fockS_re_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (fockS f f).re := by
  unfold fockS
  rw [Complex.re_sum]
  refine Finset.sum_pos (fun m hm => ?_) (support_nonempty.mpr hf)
  have hc : f.coeff m ≠ 0 := mem_support_iff.mp hm
  have hm0 : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
  have e : star (f.coeff m) * f.coeff m * (mfact m : ℂ) = ((Complex.normSq (f.coeff m) * mfact m : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]; simp
  rw [e, Complex.ofReal_re]
  exact mul_pos (Complex.normSq_pos.mpr hc) (by exact_mod_cast hm0)

theorem invNorm_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    invNorm hn ν ⟨hw ℂ hn ν, hwMem ℂ r n hn ν hν⟩ = 1 := by
  rw [invNorm, div_self (fockS_re_pos (hwNe ℂ r n hn ν)).ne', Real.sqrt_one]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceSubstitution
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistChoiceExample
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {fc : DefSub A → DefFace Bs}

structure RefInputs (X : CxData A) (cr : Crd A fc) : Prop where

  M_lat : ∀ j, Submodule.IsLattice K (X.M false j)

  T_lat : ∀ j, Submodule.IsLattice K ((lv (fc X.zs) false).Tl j Bs.μ0)

  form_nondeg : ∀ j, ((lv (fc X.zs) false).HT j Bs.μ0).det ≠ 0

  w_inj : ∀ j, Function.Injective (X.w0C false j)

  theta_inj : ∀ j, Function.Injective (X.tC cr false j Bs.μ0)

  theta_range : ∀ j, LinearMap.range (X.tC cr false j Bs.μ0) = LinearMap.range (X.w0C false j)

  theta_rat : ∀ j, IsRat Bs.v0.embedding (X.liftMatC cr false j Bs.μ0)

def ContentSupport (N : IndefNum Bs) (X'' : ℝ) (d g₁ g₂ : ℕ) : Prop :=
  ∀ w j, N.F0 w j ≠ 0 → (plc w : ℝ) ≤ X'' ∨ plc w = d ∨ plc w = g₁ ∨ plc w = g₂

def retuple (X : CxData A) (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup) (Tw : Finset (HeightOneSpectrum (𝓞 K))) : CxData A :=
  { X with μ := μ, Tw := Tw }

def TwistChoice (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (tw : HeightOneSpectrum (𝓞 K) → Bs.Tup) : Prop :=
  (∀ w, X.W1 cr N w → tw w ≠ Bs.μ0) ∧ ∀ w, X.W1 cr N w → tw (conjPl w) = tw w

def FinAt (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) : Prop :=
  {w | X.W1 cr N w}.Finite ∧ (∀ w, X.W1 cr N (conjPl w) ↔ X.W1 cr N w) ∧
    ∀ tw, TwistChoice X cr N tw →
      ∃ (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup) (Tw : Finset (HeightOneSpectrum (𝓞 K))), (retuple X μ Tw).MuDef cr N tw

def FinLemma : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (A : DefAmb Bs) (fc : DefSub A → DefFace Bs)
    (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (X'' : ℝ) (d g₁ g₂ : ℕ),
    RefInputs X cr → ContentSupport N X'' d g₁ g₂ → FinAt X cr N

theorem W1_retuple (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup)
    (Tw : Finset (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 K)) :
    (retuple X μ Tw).W1 cr N w ↔ X.W1 cr N w := Iff.rfl

def FiveSet (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ j, (X.data cr false).Iw j Bs.μ0 w ≠ 0 ∨ (X.data cr false).Iw j Bs.μ0 (conjPl w) ≠ 0 ∨
    jw ((lv (fc X.zs) false).HT j Bs.μ0) w ((lv (fc X.zs) false).Tl j Bs.μ0) ≠ 0 ∨ N.F0 w j ≠ 0 ∨ N.F0 (conjPl w) j ≠ 0

theorem W1_iff_fiveSet_or_fiveSet_conjPl (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) :
    X.W1 cr N w ↔ FiveSet X cr N w ∨ FiveSet X cr N (conjPl w) := by
  unfold CxData.W1 FiveSet
  rw [ValuationRepresentative.conjPl_conjPl]
  constructor
  · rintro ⟨j, h | h | h | h | h | h⟩
    · exact Or.inl ⟨j, Or.inl h⟩
    · exact Or.inl ⟨j, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨j, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inr ⟨j, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨j, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact Or.inl ⟨j, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩
  · rintro (⟨j, h⟩ | ⟨j, h⟩) <;> exact ⟨j, by tauto⟩

theorem refInputs_of_links (X : CxData A) (cr : Crd A fc) (wf : (lv (fc X.zs) false).WF) (hM : X.MLat false)
    (hK : X.KForm false) (hE : X.EWnorm false) (hp : X.H4pos) (h5 : X.H5 cr false) (hr : X.RATth cr false) :
    RefInputs X cr where
  M_lat := hM
  T_lat j := wf.Tl_lat j _
  form_nondeg j := by
    obtain ⟨hu, he⟩ := wf.XT_herm j Bs.μ0
    intro h0
    have h1 : (((lv (fc X.zs) false).HT j Bs.μ0).map Bs.v0.embedding).det = 0 := by
      have := (Bs.v0.embedding).map_det ((lv (fc X.zs) false).HT j Bs.μ0)
      rw [h0, map_zero] at this
      exact this.symm
    rw [← he, Matrix.det_mul, Matrix.det_conjTranspose] at h1
    have h2 : (((lv (fc X.zs) false).XT j Bs.μ0 Bs.v0)⁻¹).det ≠ 0 :=
      (Matrix.isUnit_nonsing_inv_det _ (hu Bs.v0)).ne_zero
    exact mul_ne_zero (star_ne_zero.2 h2) h2 h1
  w_inj j := by
    have hw : Function.Injective (X.wC false j Bs.v0) :=
      by
        rw [injective_iff_map_eq_zero]
        intro c hc
        have hc' : ∑ i, c i • X.bW false j Bs.v0 i = 0 := by
          simpa [CxData.wC, lin, Fintype.linearCombination_apply] using hc
        funext i
        exact Fintype.linearIndependent_iff.1 (hK j Bs.v0).1 c hc' i
    have he : Function.Injective (X.eW false j) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h := hE j x x
      rw [hx, inner_zero_left] at h
      have hn : ((X.nP false : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp.2.2 false).ne'
      exact inner_self_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left hn)
    exact he.comp hw
  theta_inj j := (h5 j _).1
  theta_range j := (h5 j _).2
  theta_rat j := hr j _

namespace Examples₂

variable (K) (v0 : InfinitePlace K)

def base : DefBase K := ⟨⊤, v0, Bool, false, Unit, inferInstance, Unit, inferInstance⟩

def stdLat : Submodule (𝓞 K) (Fin 1 → K) := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin 1)))

omit [StarRing K] in
theorem stdLat_isLattice : Submodule.IsLattice K (stdLat K) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin 1)).span_eq]
    exact Submodule.span_mono Submodule.subset_span

def amb : DefAmb (base K v0) :=
  ⟨fun _ => K, fun _ => inferInstance, fun _ => inferInstance, fun _ => Unit, fun _ _ => 1, fun _ => ⊤,
    fun _ _ => K, fun _ _ => inferInstance, fun _ _ => inferInstance, fun _ _ => Unit, fun _ _ _ => 1, fun _ _ => ⊤⟩

def side : DefSide (base K v0) :=
  ⟨fun _ => 1, fun _ => 1, fun _ => stdLat K, fun _ => 1, fun _ => 1, fun _ _ => 1, fun _ _ => ⊤,
    fun _ _ => 1, fun _ _ => 2, fun _ _ _ => 1, fun _ _ => stdLat K, fun _ _ _ => ⊤⟩

def face : DefSub (amb K v0) → DefFace (base K v0) := fun _ =>
  ⟨side K v0, side K v0, ⟨Empty, fun _ => 0, fun u => u.elim, fun u => u.elim⟩,
    ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊤⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

def crd : Crd (amb K v0) (face K v0) where
  toR _ b _ := match b with
    | false => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
    | true => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
  toL _ b _ _ := match b with
    | false => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
    | true => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)

def cx : CxData (amb K v0) where
  FC _ := ℂ
  jR _ := v0.embedding.toSemilinearMap
  EE := ℂ
  Θ _ := LinearMap.id
  EEp _ := ⊤
  EEl _ := ⊤
  FLC _ _ := ℂ
  jL _ _ := v0.embedding.toSemilinearMap
  W _ := ℂ
  θ' _ _ := LinearMap.id
  Wp _ _ := ⊤
  dW _ _ := 1
  WC _ _ _ := ℂ
  bW _ _ _ _ := 1
  eW _ _ := LinearMap.id
  M _ _ := stdLat K
  nP _ := 1
  μ _ := false
  Tw := ∅
  κ _ := 1
  lam _ _ _ _ := 1
  err0 _ _ := 0

theorem lin_one_inj : Function.Injective (lin (fun _ : Fin 1 => (1 : ℂ))) := by
  intro x y h
  funext i
  fin_cases i
  simpa [lin, Fintype.linearCombination_apply] using h

theorem exampleTwistChoice_w0C (j : Unit) : (cx K v0).w0C false j = lin (fun _ : Fin 1 => (1 : ℂ)) := rfl

theorem tC_eq (j : Unit) : (cx K v0).tC (crd K v0) false j false = lin (fun _ : Fin 1 => (1 : ℂ)) := by
  change lin (fun k : Fin 1 => v0.embedding ((Pi.single k (1 : K) : Fin 1 → K) 0)) = _
  congr 1
  funext k
  fin_cases k
  simp

theorem refInputs : RefInputs (cx K v0) (crd K v0) where
  M_lat _ := stdLat_isLattice K
  T_lat _ := stdLat_isLattice K
  form_nondeg _ := by
    change (2 : Matrix (Fin 1) (Fin 1) K).det ≠ 0
    rw [Matrix.det_unique]
    change ((2 : ℕ) : Matrix (Fin 1) (Fin 1) K) default default ≠ 0
    simp [Matrix.natCast_apply, Matrix.ofNat_apply]
  w_inj j := lin_one_inj
  theta_inj j := (tC_eq K v0 j).symm ▸ lin_one_inj
  theta_range j := congrArg LinearMap.range (tC_eq K v0 j)
  theta_rat j := by
    intro i k
    have h : (cx K v0).liftMatC (crd K v0) false j false =
        relMat (lin (fun _ : Fin 1 => (1 : ℂ))) (lin (fun _ : Fin 1 => (1 : ℂ))) :=
      congrArg (relMat (lin (fun _ : Fin 1 => (1 : ℂ)))) (tC_eq K v0 j)
    have h1 : ∀ y, solve (lin (fun _ : Fin 1 => (1 : ℂ))) (lin (fun _ : Fin 1 => (1 : ℂ)) y) = y := by
      intro y
      have he : ∃ z, lin (fun _ : Fin 1 => (1 : ℂ)) z = lin (fun _ : Fin 1 => (1 : ℂ)) y := ⟨y, rfl⟩
      unfold solve
      rw [dif_pos he]
      exact lin_one_inj he.choose_spec
    have h2 : ∀ i k : Fin 1, relMat (lin (fun _ : Fin 1 => (1 : ℂ))) (lin (fun _ : Fin 1 => (1 : ℂ))) i k = 1 := by
      intro i k
      rw [relMat, Matrix.of_apply, h1, Subsingleton.elim i k, Pi.single_eq_same]
    exact ⟨1, (map_one _).trans ((h2 i k).symm.trans (congrFun (congrFun h i) k).symm)⟩

end Examples₂

end GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample
end
end

