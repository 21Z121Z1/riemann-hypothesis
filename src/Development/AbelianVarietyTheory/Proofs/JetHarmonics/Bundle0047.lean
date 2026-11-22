import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0044

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory
namespace DSInequiv

open PI.DSInfCharCap

lemma eq_of_capP {n : ℕ} (mu mu' : Fin n → ℝ) (h : StrictAnti mu) (h' : StrictAnti mu')
    (e : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y) :
    mu = mu' := by
  have key : ∀ (a b : Fin n → ℝ),
      (∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (b s : ℂ)) Y) →
      Set.range a ⊆ Set.range b := by
    rintro a b e _ ⟨s, rfl⟩
    have h0 : Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) (-(a s : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [e] at h0
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨t, ?_⟩
    have : (b t : ℂ) = (a s : ℂ) := by linear_combination ht
    exact_mod_cast this
  have hr : Set.range mu = Set.range mu' :=
    Set.Subset.antisymm (key _ _ e) (key _ _ fun Y => (e Y).symm)
  have h1 : StrictMono (fun s => -mu s) := fun a b hab => neg_lt_neg (h hab)
  have h2 : StrictMono (fun s => -mu' s) := fun a b hab => neg_lt_neg (h' hab)
  have hr' : Set.range (fun s => -mu s) = Set.range (fun s => -mu' s) := by
    have := congrArg (fun S => Neg.neg '' S) hr
    simp only [← Set.range_comp] at this
    exact this
  have := (h1.range_inj h2).mp hr'
  funext s
  exact neg_injective (congrFun this s)

section
variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def toReal (V : H ≃L[ℂ] H') : H ≃L[ℝ] H' :=
  { V.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := V.continuous
    continuous_invFun := V.symm.continuous }

lemma dsig_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inG ε X) (v : H) :
    V (PI.PhMeasCore.dsig τ X v) = PI.PhMeasCore.dsig τ' X (V v) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => τ' (NormedSpace.exp ((t : ℂ) • X)) (V v)) =
      (toReal V) ∘ (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    exact (hV _ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t) v).symm
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

lemma dsigC_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : V (dsigC ε τ Y v) = dsigC ε τ' Y (V v) := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hH := Formalism.REAL.Jm_conjTranspose ε
  have hJ' := Formalism.REAL.f1alg_JJ_left ε
  unfold dsigC
  rw [map_add, map_smul, dsig_equiv V hV, dsig_equiv V hV]
  · rw [Formalism.REAL.f1alg_inG_iff]
    have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp [Complex.conj_I]
    simp only [thetaJ, conjTranspose_smul, hs, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    module
  · rw [Formalism.REAL.f1alg_inG_iff]
    have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [thetaJ, conjTranspose_smul, hs, conjTranspose_add, conjTranspose_neg, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    module

lemma dsigCW_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : V (dsigCW ε τ w v) = dsigCW ε τ' w (V v) := by
  induction w with
  | nil => rfl
  | cons Y w ih => simp only [dsigCW]; rw [dsigC_equiv V hV, ih]

lemma actU_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : V (actU ε τ p v) = actU ε τ' p (V v) := by
  unfold actU Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, dsigCW_equiv V hV]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma smooth_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) :
    V v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv g₀ hg₀
  refine ⟨U, fun g => V (F g), hU, hm, ?_, fun g hg hg' => ?_⟩
  · exact ((toReal V).contDiff).comp_contDiffOn hF
  · exact (hV g hg' v).symm.trans (congrArg V (hE g hg hg'))

lemma smooth_conj {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hA : Pᴴ * A * P = B) {v : H}
    (hv : PI.UpqRep.SmoothOnH B (fun g => τ g v)) :
    v ∈ PI.PhMeasCore.smoothVecs A (fun g => τ (P⁻¹ * g * P)) := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hmem : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * A * g = A → PI.UpqRep.inUH B (P⁻¹ * g * P) := by
    intro g hg
    unfold PI.UpqRep.inUH
    have h1 : P * (P⁻¹ * g * P) = g * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    calc (P⁻¹ * g * P)ᴴ * B * (P⁻¹ * g * P)
        = (P * (P⁻¹ * g * P))ᴴ * A * (P * (P⁻¹ * g * P)) := by
          rw [← hA, conjTranspose_mul P]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * (gᴴ * A * g) * P := by rw [h1, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = B := by rw [hg, hA]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => P⁻¹ * g * P
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by simp }
  let L' := LinearMap.toContinuousLinearMap L
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv _ (hmem g₀ hg₀)
  refine ⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, hF.comp_continuousLinearMap L', fun g hg hg' => ?_⟩
  exact hE _ hg (hmem g hg')

lemma eq_of_equiv (hc : DSInfCharCap) {mu mu' : Fin n → ℝ} (hm : Formalism.QuantumDeterminants.IsHCParam mu)
    (hm' : Formalism.QuantumDeterminants.IsHCParam mu') (h : PI.UpqRep.IsDS ε mu τ) (h' : PI.UpqRep.IsDS ε mu' τ')
    (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) (h0 : v ≠ 0) : mu = mu' := by
  refine eq_of_capP mu mu' hm.1 hm'.1 fun Y => ?_
  have e1 := hc n ε mu H τ hm h v hv Y
  have e2 := hc n ε mu' H' τ' hm' h' (V v) (smooth_equiv V hV hv) Y
  rw [← actU_equiv V hV, e1, map_smul] at e2
  exact smul_left_injective ℂ (by simpa using h0) e2

lemma inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ PI.UpqRep.UJset ε) (hb : b ∈ PI.UpqRep.UJset ε) :
    a * b ∈ PI.UpqRep.UJset ε := by
  show (a * b)ᴴ * PI.UpqRep.Jm ε * (a * b) = PI.UpqRep.Jm ε
  have ha' : aᴴ * PI.UpqRep.Jm ε * a = PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * PI.UpqRep.Jm ε * b = PI.UpqRep.Jm ε := hb
  calc _ = bᴴ * (aᴴ * PI.UpqRep.Jm ε * a) * b := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

lemma cayley_quot {B P Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (hP : Pᴴ * PI.UpqRep.Jm ε * P = B)
    (hQ' : Qᴴ * PI.UpqRep.Jm ε * Q = B) : P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  show (P * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  calc _ = (Q⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * Q⁻¹ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Q * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (Q * Q⁻¹) := by
      rw [hP, ← hQ', conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

end

lemma exists_kfin {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : Rep k r)
    {P : Mx k r} (hP : PI.UpqRep.IsCayleyU k r ε P) (h : PI.UpqRep.IsDS ε mu (fun g => R.σ (P⁻¹ * g * P))) :
    ∃ v, R.KFin v ∧ v ≠ 0 := by
  obtain ⟨S, hfin, hst, -, ⟨v, hvS, hv0, -⟩, -⟩ := h.2.2.2.2.2.1
  refine ⟨v, ⟨S, hfin, hvS, ?_⟩, hv0⟩
  rintro g ⟨hg, hgu⟩ x hx
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : star P * P = 1 := Unitary.star_mul_self_of_mem hP.2
  have hPP' : P * star P = 1 := Unitary.mul_star_self_of_mem hP.2
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hPP
  have hgu' : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hgu
  have hu : P * g * star P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hgu') (Unitary.star_mem hP.2)
  have hJ : (P * g * star P)ᴴ * PI.UpqRep.Jm ε * (P * g * star P) = PI.UpqRep.Jm ε := by
    have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
    have hc := hP.1.2
    rw [Matrix.star_eq_conjTranspose] at hPP' ⊢
    calc _ = P * (gᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * g) * Pᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (P * Pᴴ) * PI.UpqRep.Jm ε * (P * Pᴴ) := by
          rw [hc, hg', ← hc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP']; simp
  have hK : P * g * star P ∈ PI.UpqRep.Kset ε := by
    refine ⟨hu, ?_⟩
    have h1 : (P * g * star P) * (P * g * star P)ᴴ = 1 := Unitary.mul_star_self_of_mem hu
    generalize P * g * star P = m at hJ h1
    calc m * PI.UpqRep.Jm ε = m * (mᴴ * PI.UpqRep.Jm ε * m) := by rw [hJ]
      _ = (m * mᴴ) * PI.UpqRep.Jm ε * m := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.one_mul]
  have := hst _ hK x hx
  have e : P⁻¹ * (P * g * star P) * P = g := by
    rw [hinv]
    calc _ = (star P * P) * g * (star P * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPP]; simp
  simpa only [e] using this

theorem param_eq_of_equiv : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  intro hy k r ε mu mu' R R' hR hR' U hU
  obtain ⟨hm, P, hP, h⟩ := hR
  obtain ⟨hm', Q, hQ, h'⟩ := hR'
  obtain ⟨v, hv, hv0⟩ := exists_kfin R hP h
  have hs := hy.1.2.2.1 k r ε mu R.H R.σ hm ⟨P, hP, h⟩ v hv
  have hs' := smooth_conj (A := Formalism.REAL.Jm ε) hP.1.1 hP.1.2 hs
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hdQ := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  have p1 := Matrix.mul_nonsing_inv _ hdP
  have q1 := Matrix.mul_nonsing_inv _ hdQ
  have p2 := Matrix.nonsing_inv_mul _ hdP
  have q2 := Matrix.nonsing_inv_mul _ hdQ
  have p3 : ∀ B : Mx k r, P⁻¹ * (P * B) = B := fun B => by rw [← Matrix.mul_assoc, p2, Matrix.one_mul]
  have q3 : ∀ B : Mx k r, Q⁻¹ * (Q * B) = B := fun B => by rw [← Matrix.mul_assoc, q2, Matrix.one_mul]
  have p4 : ∀ B : Mx k r, P * (P⁻¹ * B) = B := fun B => by rw [← Matrix.mul_assoc, p1, Matrix.one_mul]
  have ha := cayley_quot hQ.1.1 hP.1.2 hQ.1.2
  have hb := cayley_quot hP.1.1 hQ.1.2 hP.1.2
  obtain ⟨⟨hone, hmul⟩, -⟩ := h'.2.2.1
  set τ' : Mx k r → (R'.H →L[ℂ] R'.H) := fun g => R'.σ (Q⁻¹ * g * Q) with hτ'
  have hmul' : ∀ a ∈ PI.UpqRep.UJset ε, ∀ b ∈ PI.UpqRep.UJset ε, ∀ x, τ' a (τ' b x) = τ' (a * b) x := by
    intro a ha b hb x
    rw [hmul a ha b hb]; rfl
  have hab : (P * Q⁻¹) * (Q * P⁻¹) = 1 := by simp only [Matrix.mul_assoc, q3, p1]
  have hba : (Q * P⁻¹) * (P * Q⁻¹) = 1 := by simp only [Matrix.mul_assoc, p3, q1]
  let A : R'.H ≃L[ℂ] R'.H := ContinuousLinearEquiv.equivOfInverse (τ' (P * Q⁻¹)) (τ' (Q * P⁻¹))
    (fun x => by rw [hmul' _ hb _ ha, hba, hone]; rfl) (fun x => by rw [hmul' _ ha _ hb, hab, hone]; rfl)
  refine eq_of_equiv hy.2.2.1 hm hm' h h' (U.toContinuousLinearEquiv.trans A) ?_ hs' hv0
  intro g hg x
  have hg' : g ∈ PI.UpqRep.UJset ε := hg
  have hG : P⁻¹ * g * P ∈ GG k r := by
    show (P⁻¹ * g * P)ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * g * P) = PI.UpqRep.Hpk k r
    have hgg : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have hc := hP.1.2
    calc _ = (P * (P⁻¹ * g * P))ᴴ * PI.UpqRep.Jm ε * (P * (P⁻¹ * g * P)) := by
          rw [← hc, conjTranspose_mul P]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * P := by
          simp only [Matrix.mul_assoc, p4, conjTranspose_mul g]
      _ = _ := by rw [hgg, hc]
  show τ' (P * Q⁻¹) (U (R.σ (P⁻¹ * g * P) x)) = τ' g (τ' (P * Q⁻¹) (U x))
  have e : R'.σ (P⁻¹ * g * P) = τ' (Q * P⁻¹ * g * (P * Q⁻¹)) := by
    simp only [hτ', Matrix.mul_assoc, q3, q2, Matrix.mul_one]
  rw [hU _ hG, e, hmul' _ ha _ (inUJ_mul (inUJ_mul hb hg') ha), hmul' _ hg' _ ha]
  congr 2
  simp only [Matrix.mul_assoc, q3, p4]

end DSInequiv
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LengthCont

variable {n ι : Type} [Fintype n] [DecidableEq n]

def dst (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (A : Matrix n n ℂ) : ℝ :=
  Metric.infDist (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)
    (Submodule.span ℂ ((fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s) : Set _)

def opn (M : Matrix n n ℂ) : ℝ := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖

lemma opn_cont : Continuous (opn (n := n)) := by

  let L : Matrix n n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun M => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
      map_add' := fun M N => map_add _ M N
      map_smul' := fun c M => map_smul _ c M }
  exact continuous_norm.comp (LinearMap.continuous_of_finiteDimensional L)

lemma opn_one [Nonempty n] : opn (1 : Matrix n n ℂ) = 1 := by
  unfold opn
  rw [map_one]
  exact norm_one

private lemma infDist_image_le_opNorm_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (y : E) (K : Set E) (hK : K.Nonempty) :
    Metric.infDist (T y) (T '' K) ≤ ‖T‖ * Metric.infDist y K := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (‖T‖ + 1) := by positivity
  obtain ⟨p, hp, hd⟩ := (Metric.infDist_lt_iff hK).1 (lt_add_of_pos_right (Metric.infDist y K) hδ)
  have hTε : ‖T‖ * (ε / (‖T‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg T]
  calc Metric.infDist (T y) (T '' K) ≤ dist (T y) (T p) :=
        Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem T hp)
    _ ≤ ‖T‖ * dist y p := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact T.le_opNorm _
    _ ≤ ‖T‖ * (Metric.infDist y K + ε / (‖T‖ + 1)) := by gcongr
    _ ≤ ‖T‖ * Metric.infDist y K + ε := by rw [mul_add]; linarith

lemma dst_mul_le (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (M A : Matrix n n ℂ) :
    dst x f s (M * A) ≤ opn M * dst x f s A := by
  unfold dst
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
  have key : ∀ v : n → ℂ, (WithLp.toLp 2 ((M * A) *ᵥ v) : EuclideanSpace ℂ n) =
      T (WithLp.toLp 2 (A *ᵥ v)) := fun v => by
    rw [← Matrix.mulVec_mulVec]; rfl
  simp only [key]
  set S : Set (EuclideanSpace ℂ n) := (fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s
  have himg : (fun b => T (WithLp.toLp 2 (A *ᵥ f b))) '' s = T '' S := (Set.image_image _ _ _).symm
  rw [himg]

  have hsub : T '' (Submodule.span ℂ S : Set _) ⊆ (Submodule.span ℂ (T '' S) : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.apply_mem_span_image_of_mem_span (T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) hp
  calc Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (Submodule.span ℂ (T '' S) : Set _)
      ≤ Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (T '' (Submodule.span ℂ S : Set _)) :=
        Metric.infDist_le_infDist_of_subset hsub ⟨T 0, 0, Submodule.zero_mem _, rfl⟩
    _ ≤ ‖T‖ * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) :=
        infDist_image_le_opNorm_mul T _ _ ⟨0, Submodule.zero_mem _⟩
    _ = opn M * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) := rfl

lemma dst_inv_continuousOn [Nonempty n] (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) :
    ContinuousOn (fun g : Matrix n n ℂ => dst x f s g⁻¹) {g | IsUnit g.det} := by
  set U : Set (Matrix n n ℂ) := {g | IsUnit g.det}

  have hinv : ContinuousOn (fun g : Matrix n n ℂ => g⁻¹) U := by
    have h : (fun g : Matrix n n ℂ => g⁻¹) = fun g => (g.det)⁻¹ • g.adjugate := by
      funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    exact (continuous_id.matrix_det.continuousOn.inv₀ fun g hg => hg.ne_zero).smul
      continuous_id.matrix_adjugate.continuousOn
  intro g0 hg0
  have hg0' : IsUnit g0.det := hg0
  set a0 := dst x f s g0⁻¹

  have hu : Filter.Tendsto (fun g => opn (g⁻¹ * g0)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : ContinuousWithinAt (fun g => opn (g⁻¹ * g0)) U g0 :=
      opn_cont.continuousAt.comp_continuousWithinAt ((hinv g0 hg0).mul continuousWithinAt_const)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.tendsto
    rwa [h1] at this
  have hv : Filter.Tendsto (fun g => opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : Continuous fun g => opn (g0⁻¹ * g) := opn_cont.comp (continuous_const.mul continuous_id)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.continuousWithinAt (s := U) (x := g0) |>.tendsto
    rwa [h1] at this
  have hup : ∀ g ∈ U, dst x f s g⁻¹ ≤ opn (g⁻¹ * g0) * a0 := by
    intro g _
    have h := dst_mul_le x f s (g⁻¹ * g0) g0⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ hg0', mul_one] at h
  have hlow : ∀ g ∈ U, a0 ≤ opn (g0⁻¹ * g) * dst x f s g⁻¹ := by
    intro g hg
    have h := dst_mul_le x f s (g0⁻¹ * g) g⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ (show IsUnit g.det from hg), mul_one] at h
  have hpos : ∀ᶠ g in nhdsWithin g0 U, 0 < opn (g0⁻¹ * g) := hv.eventually (lt_mem_nhds one_pos)
  have hL : Filter.Tendsto (fun g => a0 / opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds a0) := by
    have := (tendsto_const_nhds (x := a0)).div hv one_ne_zero
    rwa [div_one] at this
  have hR : Filter.Tendsto (fun g => opn (g⁻¹ * g0) * a0) (nhdsWithin g0 U) (nhds a0) := by
    have := hu.mul_const a0
    rwa [one_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hR ?_ (eventually_nhdsWithin_of_forall hup)
  filter_upwards [hpos, eventually_nhdsWithin_of_forall hlow] with g hg1 hg2
  rw [div_le_iff₀ hg1, mul_comm]
  exact hg2

theorem lenA_continuousOn : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z → ∀ a, ContinuousOn (fun g => lenA k r z g a) (GG k r) := by
  intro k r z _ _ a

  have hsub : GG k r ⊆ {g : Mx k r | IsUnit g.det} := by
    intro g hg
    have h1 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hdet : (Formalism.QuantumDeterminants.Hpk k r).det * (Formalism.QuantumDeterminants.Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    show IsUnit g.det
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h2
    rw [← h2, mul_zero] at hdet
    exact zero_ne_one hdet
  exact (dst_inv_continuousOn (Formalism.QuantumDeterminants.fvec k r z a) (Formalism.QuantumDeterminants.fvec k r z) {b | b < a}).mono hsub

end GlobalTheory.LengthCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.UnipotentRadicalHaar

theorem eq_smul_of_twoSided {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : B.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • ν := by
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν.finite_compact K hK⟩
  obtain ⟨c, -, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique hU hμ
    (ν := ν) ⟨inferInstance, hν.ne_zero, hν.conc, hν.left⟩
  exact ⟨c, c1, e⟩

theorem unimodular_normal : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.IsRightInvM (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsFiniteMeasure μW ∧ PI.IsRightInvM (Formalism.QuantumDeterminants.Nset k r) μN ∧ (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, h * m * h⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) ∧ ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, μN.map (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h * Matrix.of x * h⁻¹) i j : Formalism.QuantumDeterminants.Mt k r)) = μN := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨νW, hνW⟩ := P.weyl_haar_exists k r z hz hT
  obtain ⟨νN, hνN⟩ := P.unipotent_haar_exists k r
  obtain ⟨a, a1, ea⟩ := eq_smul_of_twoSided (P.B2x3.closedW k r z) hW hνW
  obtain ⟨b, -, eb⟩ := eq_smul_of_twoSided (P.B2x2.closedN k r) hN hνN
  refine ⟨fun s hs => ?_, ⟨?_⟩, fun s hs => ?_,
    fun h hh m hm => (Formalism.QuantumDeterminants.uWNormal k r z hz h hh m hm).1, fun h hh => ?_⟩
  · rw [ea, Measure.map_smul]
    exact congrArg (a • ·) (hνW.right s hs)
  · have hK : IsCompact (Formalism.QuantumDeterminants.UWset k r z) := P.weyl_subgroup_compact k r z hz hT
    have h1 : νW (Formalism.QuantumDeterminants.UWset k r z) < ⊤ := hνW.finite_compact _ hK
    have h2 : νW Set.univ ≤ νW (Formalism.QuantumDeterminants.UWset k r z) + νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    have h3 : νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ = 0 := hνW.conc
    rw [h3, add_zero] at h2
    rw [ea, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top a1.lt_top (h2.trans_lt h1)
  · rw [eb, Measure.map_smul]
    exact congrArg (b • ·) (hνN.right s hs)
  · rw [eb, Measure.map_smul]
    exact congrArg (b • ·) (P.b2_conjInvRaw_proof k r z νN hz hT hνN h hh)

end GlobalTheory.UnipotentRadicalHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBessel
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bessel_nonzero_on_translates : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDS ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  intro hH k r ε mu R Wp _ _ _ _ z π l hds hB hnz
  obtain ⟨⟨-, -, hKF, -⟩, hCyc, -⟩ := hH
  have hex : ∃ w0, PI.UpqRep.IsLowUnitH k r ε mu R.σ w0 := by
    obtain ⟨P, hP, -, -, -, -, -, ⟨S, hS⟩, -⟩ := hds.2
    obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, P, hP, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · exact Submodule.smul_mem _ _ (Submodule.mem_sSup.mpr fun N hN => hN S hS hvS)
  obtain ⟨w0, hlow⟩ := hex
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  by_contra hcon
  push_neg at hcon
  obtain ⟨w, hw, hlw⟩ := hnz
  refine hlw (Formalism.FourierDecayAlt.P.bessel_ne_zero_of_cyclic_orbit hCyc hKF k r ε mu R.H R.σ w0 Wp z Formalism.QuantumDeterminants.cStd π hds.1 hds.2 hlow
    l hB (fun x hx => hcon x ?_) w hw)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hg, w0, hwK, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOne
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix

namespace GlobalTheory.BesselNorm

theorem hilbertSchmidt_normInv : Formalism.FourierDecayAlt.ThreeDimData.NormInv := fun _ _ =>
  ⟨fun x y => PI.PolynomialProperness.GN.gN_mul_le x y,
    fun _ hx => ⟨PI.PolynomialProperness.GN.gN_inv hx, PI.PolynomialProperness.GN.gN_ge_one hx⟩⟩

end GlobalTheory.BesselNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlProjectionLevelSumSqLe
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_proj_and_sum_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, (∀ s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w))) ∧ ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c
  exact ⟨GlobalTheory.T.unitary_glModule_proj_dual_tensor_level_add_two M n ε E N F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c,
    GlobalTheory.T.sum_normSq_projections_tensor_unitary_gl_le M n ε E N F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c⟩

end GlobalTheory
end

