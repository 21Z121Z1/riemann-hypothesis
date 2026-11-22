import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumProdLeOfCoord
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem norm_sum_prod_le_of_coord {K : Type*} [NormedCommRing K] {g m : ℕ} (F G : Fin m → Fin g → ℕ → K)
    (c : Fin m → K) (B : ℝ)
    (step : ∀ (i : Fin g) (c' : Fin m → K), (∀ n, ‖∑ j, c' j * F j i n‖ ≤ B) → ∀ n, ‖∑ j, c' j * G j i n‖ ≤ B)
    (h : ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, F j i (ν i)‖ ≤ B) (ν : Fin g → ℕ) :
    ‖∑ j, c j * ∏ i, G j i (ν i)‖ ≤ B := by
  classical
  have key : ∀ I : Finset (Fin g), ∀ ν : Fin g → ℕ,
      ‖∑ j, c j * ∏ i, (if i ∈ I then G j i (ν i) else F j i (ν i))‖ ≤ B := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa using h
    | insert i₀ I hi ih =>
      intro ν
      have hs := step i₀
        (fun j => c j * ∏ i ∈ Finset.univ.erase i₀, (if i ∈ I then G j i (ν i) else F j i (ν i))) ?_ (ν i₀)
      · convert hs using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi']
        · simp
      · intro n
        convert ih (Function.update ν i₀ n) using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
        · simp [hi]
  simpa using key Finset.univ ν

theorem translate_norm_prod_le : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (θ : ℂ → ℂ), ThetaLaws ι d ω θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ_[q]) (t : Fin m → Fin g → ℂ) (τ : Fin g → ℂ) (B : ℝ), (∀ j i, PrimeTo d q (t j i)) → (∀ i, PrimeTo d q (τ i)) → (∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B) → ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)‖ ≤ B := by
  intro d q _ ι ω θ hθ g m a c t τ B ht hτ h
  refine norm_sum_prod_le_of_coord
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)) c B ?_ h
  intro i c' hc n
  have := hθ.2.2 (a i) m c' (fun j => t j i) (τ i) B (fun j => ht j i) (hτ i) (fun k => by
    simpa only [map_sum, coeff_C_mul] using hc k) n
  simpa only [map_sum, coeff_C_mul] using this

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpUConstMul
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.HeisOps

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem hf_add_left (x y z : Fin g → ℂ) : hf Hm (x + y) z = hf Hm x z + hf Hm y z := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin g → ℂ) : hf Hm x (y + z) = hf Hm x y + hf Hm x z := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_zero_right (x : Fin g → ℂ) : hf Hm x 0 = 0 := by simp [hf]

theorem hf_swap (h : Hm.IsHermitian) (x y : Fin g → ℂ) : hf Hm y x = conj (hf Hm x y) := by
  simp only [hf, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : conj (Hm i j) = Hm j i := h.apply j i
  rw [e]; ring

theorem opU_opU (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z =>
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z := by
  funext z
  simp only [opU]
  rw [add_assoc z x y, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [hf_add_left, hf_add_right]
  have e := Complex.sub_conj (hf Hm x y)
  rw [hf_swap h x y]
  push_cast at e
  linear_combination (-(Real.pi : ℂ) / 2) * e

theorem opU_comm (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z => kap Hm x y * opU Hm y (opU Hm x F) z := by
  funext z
  rw [opU_opU h x y, opU_opU h y x, add_comm y x, kap, ← mul_assoc, ← Complex.exp_add, hf_swap h x y,
    Complex.conj_im]
  push_cast
  ring_nf

theorem im_eq {d : ℕ} (hd : 0 < d) (x y : Fin g → ℂ) (u v : ℤ) (h : beta d Hm x y = u + v * w0 d) :
    (hf Hm x y).im = v := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  have e := congrArg Complex.im h
  rw [beta, Complex.im_ofReal_mul] at e
  have e2 : ((u : ℂ) + v * w0 d).im = Real.sqrt d / 2 * v := by
    simp [w0, rtd]; ring
  rw [e2] at e
  exact mul_left_cancel₀ (div_ne_zero hs two_ne_zero) e

theorem opU_const_mul (c : ℂ) (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    opU Hm x (fun w => c * F w) z = c * opU Hm x F z := by
  simp only [opU]; ring

theorem opW_opW {d : ℕ} (hd : 0 < d) (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ)
    (hb : beta d Hm x y ∈ OK d) : opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F := by
  obtain ⟨u, v, huv⟩ := hb
  have him := im_eq hd x y u v huv
  have hre : (beta d Hm x y).re = u + v / 2 := by
    rw [huv]; simp [w0, rtd]; ring
  have hq : (beta d Hm (x + y) (x + y)).re = (beta d Hm x x).re + (beta d Hm y y).re + (2 * u + v) := by
    simp only [beta, Complex.re_ofReal_mul, hf_add_left, hf_add_right, Complex.add_re] at hre ⊢
    rw [hf_swap h x y, Complex.conj_re]
    linear_combination 2 * hre
  funext z
  have e : opW d Hm x (opW d Hm y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) *
      (Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm y y).re : ℂ)) * opU Hm x (opU Hm y F) z) := by
    rw [← opU_const_mul]; rfl
  rw [e, opU_opU h, him]
  simp only [opW]
  rw [hq, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u + v), ?_⟩
  push_cast
  ring

theorem contDiff_opU (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opU Hm x F) := by
  unfold opU hf
  refine (hF.comp (contDiff_id.add contDiff_const)).mul (ContDiff.cexp ?_)
  fun_prop

theorem contDiff_opW (d : ℕ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (opW d Hm x F) :=
  contDiff_const.mul (contDiff_opU x hF)

theorem heisenberg : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), 0 < d → Hm.IsHermitian → (∀ (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), opU Hm x (opU Hm y F) = (fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z) ∧ opU Hm x (opU Hm y F) = (fun z => kap Hm x y * opU Hm y (opU Hm x F) z) ∧ (beta d Hm x y ∈ OK d → opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F)) ∧ (∀ F, opU Hm 0 F = F ∧ opW d Hm 0 F = F) ∧ (∀ (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ (opU Hm x F) ∧ ContDiff ℂ ⊤ (opW d Hm x F)) ∧ (∀ x y : Fin g → ℂ, hf Hm y x = conj (hf Hm x y)) ∧ (∀ (x y : Fin g → ℂ) (u v : ℤ), beta d Hm x y = u + v * w0 d → (hf Hm x y).im = v) ∧ ∀ x y z : Fin g → ℂ, kap Hm x (y + z) = kap Hm x y * kap Hm x z ∧ kap Hm (x + y) z = kap Hm x z * kap Hm y z := by
  intro g d Hm hd h
  refine ⟨fun x y F => ⟨opU_opU h x y F, opU_comm h x y F, opW_opW hd h x y F⟩, fun F => ?_,
    fun x F hF => ⟨contDiff_opU x hF, contDiff_opW d x hF⟩, hf_swap h, im_eq hd, fun x y z => ⟨?_, ?_⟩⟩
  · constructor <;> funext z <;> simp [opW, opU, beta, hf_zero_right]
  · simp only [kap, hf_add_right, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring
  · simp only [kap, hf_add_left, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring

end GlobalTheory.HeisOps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdDetMemHaO
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude

namespace GlobalTheory.CombMinor

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]

def cMat (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) :
    Matrix (Fin s) (Fin s) (MvPolynomial (Letter Ty r n) k) :=
  Matrix.of fun ρ i : Fin s => ∑ b, C (B ρ b) * (X ⟨τ, Fin.castLE hs i, b⟩ : MvPolynomial (Letter Ty r n) k)

theorem det_mem {R : Type} [CommRing R] (S : Subring R) {s : ℕ} (M : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun π _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (S.prod_mem fun i _ => h _ _) _

theorem cMat_supported (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (S : Set (Letter Ty r n))
    (h : ∀ ρ i b, B ρ b ≠ 0 → (⟨τ, i, b⟩ : Letter Ty r n) ∈ S) :
    (cMat τ s hs B).det ∈ supported k S := by
  refine det_mem (supported k S).toSubring _ fun ρ i => ?_
  change _ ∈ supported k S
  simp only [cMat, Matrix.of_apply]
  refine Subalgebra.sum_mem _ fun b _ => ?_
  by_cases hb : B ρ b = 0
  · rw [hb, C_0, zero_mul]; exact Subalgebra.zero_mem _
  · refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
    rw [supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨_, h ρ _ b hb, rfl⟩

theorem cMat_range (O : Subring k) (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k)
    (h : ∀ ρ b, B ρ b ∈ O) :
    (cMat τ s hs B).det ∈ (MvPolynomial.map (σ := Letter Ty r n) O.subtype).range := by
  refine det_mem _ _ fun ρ i => ?_
  simp only [cMat, Matrix.of_apply]
  refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ⟨C ⟨B ρ b, h ρ b⟩, by simp⟩ ⟨X _, map_X _ _⟩

theorem cMat_rowShift [Fintype Ty] (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k)
    (σ : Ty) (i i' : Fin (r σ)) (hii : i' < i) (t : k) :
    rowShift r n k σ i i' t (cMat τ s hs B).det = (cMat τ s hs B).det := by
  rw [AlgHom.map_det]
  by_cases hτ : τ = σ
  · subst hτ
    by_cases hin : i.val < s
    · have hin' : i'.val < s := lt_trans hii hin
      let i0 : Fin s := ⟨i.val, hin⟩
      let i1 : Fin s := ⟨i'.val, hin'⟩
      have hne : i0 ≠ i1 := by
        intro h
        have := congrArg Fin.val h
        simp only [i0, i1] at this
        exact (ne_of_gt hii) (Fin.ext this)
      have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) =
          (cMat τ s hs B).updateCol i0 (fun p => cMat τ s hs B p i0 +
            (C t : MvPolynomial (Letter Ty r n) k) • cMat τ s hs B p i1) := by
        refine Matrix.ext fun p q => ?_
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
          algHom_C, algebraMap_eq, rowShift, aeval_X, Matrix.updateCol_apply, crSig_iff]
        by_cases hp : q = i0
        · subst hp
          have hc : Fin.castLE hs i0 = i := Fin.ext rfl
          have hc1 : Fin.castLE hs i1 = i' := Fin.ext rfl
          simp only [hc, hc1, if_true, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring
        · rw [if_neg hp]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [if_neg]
          intro h
          apply hp
          apply Fin.ext
          have := congrArg Fin.val h
          simp only [Fin.val_castLE] at this
          exact this
      rw [hmat]
      exact Matrix.det_updateCol_add_smul_self _ hne (C t)
    · have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
        refine Matrix.ext fun p q => ?_
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
          algHom_C, algebraMap_eq, rowShift, aeval_X, crSig_iff]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [if_neg]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castLE] at this
        omega
      rw [hmat]
  · have hmat : (rowShift r n k σ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
      refine Matrix.ext fun p q => ?_
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
        algHom_C, algebraMap_eq, rowShift, aeval_X]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [if_neg (crSig_ne hτ)]
    rw [hmat]

theorem cMat_hom [Fintype Ty] (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (σ : Ty) (i0 : ℕ) :
    IsWeightedHomogeneous (crW (r := r) (n := n) σ i0) (cMat τ s hs B).det
      (if τ = σ ∧ i0 < s then 1 else 0) := by
  rw [← mem_weightedHomogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← crRowSum τ σ s i0]
  refine IsWeightedHomogeneous.prod _ _ _ fun j _ => ?_
  rw [← mem_weightedHomogeneousSubmodule]
  simp only [cMat, Matrix.of_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [C_mul']
  refine Submodule.smul_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_X k (crW (r := r) (n := n) σ i0) ⟨τ, Fin.castLE hs j, b⟩

theorem prod_det_mem_HaO : ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (O : Subring k) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (A : Type) [Fintype A] (σ : A → Ty) (s : A → ℕ) (hs : ∀ α, s α ≤ r (σ α)) (B : ∀ α, Fin (s α) → Fin n → k) (e : A → ℕ), (∀ α ρ b, B α ρ b ∈ O) → (∀ τ, cc τ ≠ τ) → (∀ α α', e α ≠ 0 → e α' ≠ 0 → σ α' = cc (σ α) → ∀ ρ ρ' b, B α ρ b = 0 ∨ B α' ρ' b = 0) → (∀ (τ : Ty) (i : Fin (r τ)), ∑ α ∈ Finset.univ.filter (fun α => σ α = τ ∧ i.val < s α), e α = a τ i) → (∏ α, (Matrix.of fun ρ i : Fin (s α) => ∑ b, MvPolynomial.C (B α ρ b) * (MvPolynomial.X ⟨σ α, Fin.castLE (hs α) i, b⟩ : MvPolynomial (Letter Ty r n) k)).det ^ e α) ∈ HaO r n k O cc isX a := by
  intro Ty _ r n k _ O cc isX a A _ σ s hs B e hO _ hdis hdeg
  change (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · let S : Set (Letter Ty r n) := {ℓ | ∃ α, e α ≠ 0 ∧ σ α = ℓ.1 ∧ ∃ ρ, B α ρ ℓ.2.2 ≠ 0}
    have hS : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ supported k S := by
      refine Subalgebra.prod_mem _ fun α _ => ?_
      by_cases he : e α = 0
      · rw [he, pow_zero]; exact Subalgebra.one_mem _
      · exact Subalgebra.pow_mem _ (cMat_supported _ _ _ _ S fun ρ i b hb =>
          (show _ ∈ S from ⟨α, he, rfl, ρ, hb⟩)) _
    generalize (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) = P at hS
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
    intro τ _ i i'
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
    by_cases hb : b = b'
    · subst hb
      have key : pderiv (⟨τ, i, b⟩ : Letter Ty r n) (pderiv (⟨cc τ, i', b⟩ : Letter Ty r n) P) = 0 := by
        by_cases hg : (⟨cc τ, i', b⟩ : Letter Ty r n) ∈ S
        · have hg' : (⟨τ, i, b⟩ : Letter Ty r n) ∉ S := by
            rintro ⟨α, he, hσ, ρ, hρ⟩
            obtain ⟨α', he', hσ', ρ', hρ'⟩ := hg
            rcases hdis α α' he he' (by rw [hσ', hσ]) ρ ρ' b with h | h
            · exact hρ h
            · exact hρ' h
          exact pderiv_eq_zero_of_notMem_vars
            (fun hv => hg' (mem_supported.1 (crPderiv_supported _ hS) hv))
        · rw [pderiv_eq_zero_of_notMem_vars (fun hv => hg (mem_supported.1 hS hv)), map_zero]
      simpa using congrArg (fun x => (1 : k) • x) key
    · simp [Matrix.one_apply_ne hb]
  · intro τ i i' hii t
    rw [map_prod]
    refine Finset.prod_congr rfl fun α _ => ?_
    rw [map_pow, cMat_rowShift _ _ _ _ _ _ _ hii]
  · intro m hm τ i
    rw [← crW_weight]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun α => (cMat (σ α) (s α) (hs α) (B α)).det ^ e α)
      (fun α => e α • (if σ α = τ ∧ i.val < s α then 1 else 0))
      (fun α _ => (cMat_hom (σ α) (s α) (hs α) (B α) τ i.val).pow (e α))
    rw [h (Finsupp.mem_support_iff.1 hm), ← hdeg τ i, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs <;> simp
  · intro m
    obtain ⟨Q, hQ⟩ : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈
        (MvPolynomial.map (σ := Letter Ty r n) O.subtype).range :=
      Subring.prod_mem _ fun α _ => Subring.pow_mem _ (cMat_range O _ _ _ _ (hO α)) _
    rw [← hQ, coeff_map]
    exact (Q.coeff m).2

end GlobalTheory.CombMinor
end
end

