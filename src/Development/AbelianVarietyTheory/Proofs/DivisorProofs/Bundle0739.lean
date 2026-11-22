import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvector
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.JointHarm

namespace GlobalTheory.FockScalarType

theorem injective_of_isFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι) :
    Function.Injective ι := by
  have key : ∀ (α : σ →₀ ℕ) (P : MvPolynomial σ ℂ), inner ℂ (ι (monomial α 1)) (ι P) =
      coeff α P * α.prod (fun _ k => (k.factorial : ℂ)) := by
    intro α P
    induction P using MvPolynomial.induction_on' with
    | add P P' h h' => simp only [map_add, inner_add_right, h, h', coeff_add, add_mul]
    | monomial β c =>
      rw [monomial_eq_smul β c, map_smul, inner_smul_right, hι, coeff_smul, coeff_monomial]
      by_cases e : α = β
      · subst e; simp
      · simp [e, Ne.symm e]
  refine (injective_iff_map_eq_zero ι).2 fun P hP => ?_
  ext α
  have h := key α P
  rw [hP, inner_zero_right, eq_comm, mul_eq_zero] at h
  refine h.resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

variable {p q r s : ℕ}

def charSub (p q r s : ℕ) (x : ℚ) : Submodule ℂ (Pol p q r s) where
  carrier := {f | ∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y f = ((x : ℂ) * Y.trace) • f}
  add_mem' := fun ha hb Y hY => by rw [map_add, ha Y hY, hb Y hY, smul_add]
  zero_mem' := fun Y _ => by simp
  smul_mem' := fun c _ ha Y hY => by rw [map_smul, ha Y hY, smul_comm]

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem isHW_of_mem {x : ℚ} {f : Pol p q r s} (h0 : f ≠ 0) (hf : f ∈ charSub p q r s x) :
    IsHW (fockAct1 p q r s) (fun _ => x) f := by
  refine ⟨h0, ?_, ?_⟩
  · simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [hf _ (isKC_Eab (by rcases a with a | a <;> trivial))]
    simp [Eab]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    have h1 : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
    have h2 : a ≠ b := by
      rintro rfl
      rcases a with a | a <;> simp [posC] at hab
    rw [hf _ (isKC_Eab h1), Eab, Matrix.trace_single_eq_of_ne _ _ _ h2]
    simp

theorem comm_parts {Y : Mat p q} (hY : IsKC Y) {Z : Mat r s} (hZ : IsPC Z) {d : ℕ}
    {v : Pol p q r s} (hv : v ∈ homog (Ln p q r s) d) :
    fockAct1 p q r s Y (upOp (kron2 p q Z) v) = upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∧
    fockAct1 p q r s Y (dnOp (kron2 p q Z) v) = dnOp (kron2 p q Z) (fockAct1 p q r s Y v) := by
  have hK : ∀ {d : ℕ} {w : Pol p q r s}, w ∈ homog (Ln p q r s) d →
      fockAct1 p q r s Y w ∈ homog (Ln p q r s) d := fun hw =>
    GlobalTheory.FockDeg.omAct_mem_homog (GlobalTheory.FockDeg.lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hY) hw
  have hc := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute p q r s).2.2 Y Z) v
  rw [Module.End.mul_apply, Module.End.mul_apply, fockAct2_eq, omAct_odd (odd_kron2 hZ),
    LinearMap.add_apply, LinearMap.add_apply, map_add] at hc
  have h1 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∈
      homog (Ln p q r s) (d + 2) :=
    Submodule.sub_mem _ (hK (upOp_homog _ d v hv)) (upOp_homog _ d _ (hK hv))
  have h2 : dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) ∈
      homog (Ln p q r s) (d - 2) :=
    Submodule.sub_mem _ (dnOp_homog _ d _ (hK hv)) (hK (dnOp_homog _ d v hv))
  have e : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) =
      dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) := by
    linear_combination hc
  have h0 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) -
      upOp (kron2 p q Z) (fockAct1 p q r s Y v) = 0 := by
    by_contra hne
    have := IsHomogeneous.inj_right h1 (e ▸ h2) hne
    omega
  exact ⟨sub_eq_zero.1 h0, (sub_eq_zero.1 (e ▸ h0)).symm⟩

theorem upOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    upOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).1, hc Y hY, map_smul]

theorem dnOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    dnOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).2, hc Y hY, map_smul]

theorem eq_zero_of_lowering {x : ℚ} {e e₀ : ℕ} {g v : Pol p q r s} (hg0 : g ≠ 0)
    (hg : g ∈ homog (Ln p q r s) e₀) (hgc : g ∈ charSub p q r s x) (he : e₀ < e)
    (hv : v ∈ homog (Ln p q r s) e) (hvc : v ∈ charSub p q r s x)
    (hd : ∀ Z : Mat r s, IsPC Z → dnOp (kron2 p q Z) v = 0) : v = 0 := by
  by_contra h0
  have h1 := isSide_one.degW_le Function.bijective_id hg (isHW_of_mem hg0 hgc)
  obtain ⟨d, hd1, hd2⟩ := isSide_one.homog_of_hw Function.bijective_id (isHW_of_mem h0 hvc)
    ((mem_harm1 v).1 fun Z hZ => by
      rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) v).2, hd Z hZ])
  obtain rfl : d = e := IsHomogeneous.inj_right hd2 hv h0
  rw [← hd1, Nat.cast_le] at h1
  omega

theorem mem_span_raising : ∀ (P Q R S : ℕ) (x : ℚ) (e e₀ : ℕ) (f g : Pol P Q R S),
    f ∈ homog (Ln P Q R S) e →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f) →
    g ≠ 0 → g ∈ homog (Ln P Q R S) e₀ →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g = ((x : ℂ) * Y.trace) • g) →
    e₀ < e →
    f ∈ Submodule.span ℂ {f' | ∃ Z : Mat R S, IsPC Z ∧
      ∃ g' ∈ homog (Ln P Q R S) (e - 2),
        (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 P Q R S Z) g'} := by
  intro p q r s x e e₀ f g hf hfc hg0 hg hgc he
  by_cases h2 : e < 2
  · rw [eq_zero_of_lowering hg0 hg hgc he hf hfc fun Z _ => dnOp_low _ e h2 f hf]
    exact Submodule.zero_mem _
  have hι := GlobalTheory.FockAlg.Model.isFockIsometry_fockEmb (Ln p q r s)
  have hinj := injective_of_isFockIP hι
  set U := Submodule.span ℂ {f' | ∃ Z : Mat r s, IsPC Z ∧
      ∃ g' ∈ homog (Ln p q r s) (e - 2),
        (∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 p q r s Z) g'} with hU
  have hle : U ≤ homog (Ln p q r s) e ⊓ charSub p q r s x := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, hZ, g', h1, h3, rfl⟩
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) g').1]
    refine ⟨?_, upOp_mem_charSub hZ h1 h3⟩
    have := upOp_homog (kron2 p q Z) _ g' h1
    rwa [show e - 2 + 2 = e by omega] at this
  have := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  obtain ⟨u, hu, ho⟩ := exists_orth (GlobalTheory.FockAlg.Model.fockEmb (Ln p q r s)) U f
  have hh := Submodule.sub_mem _ hf (hle hu).1
  have hc : f - u ∈ charSub p q r s x := Submodule.sub_mem _ hfc (hle hu).2
  have h0 : f - u = 0 := eq_zero_of_lowering hg0 hg hgc he hh hc fun Z hZ => by
    have hZ' := isPC_conjTranspose hZ
    have h1 := ho _ (Submodule.subset_span ⟨_, hZ', _, dnOp_homog (kron2 p q Z) e _ hh,
      dnOp_mem_charSub hZ hh hc, rfl⟩)
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ') _).1, inner_upOp hι (odd_kron2 hZ'),
      ← lineKroneckerRightMatrix_conjTranspose, neg_eq_zero, inner_self_eq_zero] at h1
    exact hinj (h1.trans (map_zero _).symm)
  rw [sub_eq_zero.1 h0]
  exact hu

end GlobalTheory.FockScalarType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
section
noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockDeg MvPolynomial Matrix

variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_pderiv {σ : Type} [DecidableEq σ] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι)
    (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv i P)) (ι Q) = inner ℂ (ι P) (ι (X i * Q)) := by
  rw [← inner_conj_symm, ← inner_X_mul hι, inner_conj_symm]

theorem inner_raiB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (raiB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (lowB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (-pderiv l P)) (ι Q) = -1 * inner ℂ (ι P) (ι (X l * Q))
    rw [map_neg, inner_neg_left, inner_pderiv hι, neg_one_mul]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (X l * P)) (ι Q) = 1 * inner ℂ (ι P) (ι (pderiv l Q))
    rw [inner_X_mul hι, one_mul]

theorem inner_lowB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (lowB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (raiB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (X l * P)) (ι Q) = -1 * inner ℂ (ι P) (ι (-pderiv l Q))
    rw [map_neg, inner_neg_right, inner_X_mul hι, neg_one_mul, neg_neg]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (pderiv l P)) (ι Q) = 1 * inner ℂ (ι P) (ι (X l * Q))
    rw [inner_pderiv hι, one_mul]

theorem inner_omE {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l l' : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q)) := by
  have h1 : inner ℂ (ι (raiB l (lowB l' P))) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (raiB l' (lowB l Q))) := by
    rw [inner_raiB hι, inner_lowB hι, ← mul_assoc]
    congr 1
    cases linePos l <;> cases linePos l' <;> simp
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, inner_add_left, inner_add_right,
    mul_add, h1]
  congr 1
  by_cases h : l = l'
  · subst h
    simp [inner_smul_left, inner_smul_right, map_ofNat]
  · simp [h, Ne.symm h]

theorem inner_omAct {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι)
    (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (h : ∀ l l', N l' l = (if linePos l = linePos l' then 1 else -1) * star (M l l'))
    (P Q : Pol p q r s) :
    inner ℂ (ι (omAct p q r s M P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s N Q)) := by
  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [inner_omE hι, h, starRingEnd_apply]
  ring

theorem adjZ_apply (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = (if sameBlock b a then 1 else -1) * star (Z b a) := by
  have hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [adjZ, hJ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem fock_adjoints : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι →
    (∀ (l l' : Ln p q r s) (P Q : Pol p q r s), inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q))) ∧
    (∀ (Z : Mat p q) (P Q : Pol p q r s), inner ℂ (ι (fockAct1 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct1 p q r s (adjZ Z) Q))) ∧
    (∀ (Z : Mat r s) (P Q : Pol p q r s), inner ℂ (ι (fockAct2 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct2 p q r s (adjZ Z) Q))) := by
  intro p q r s H _ _ ι hι
  refine ⟨inner_omE hι, fun Z P Q => ?_, fun Z P Q => ?_⟩
  · rw [fockAct1_eq, fockAct1_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : c = d
    · subst e
      simp [kr1, adjZ_apply, linePos_eq_iff_fst]
    · simp [kr1, e, Ne.symm e]
  · rw [fockAct2_eq, fockAct2_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : a = b
    · subst e
      simp [kr2, adjZ_apply, linePos_eq_iff_snd]
    · simp [kr2, e, Ne.symm e]

end GlobalTheory.FockAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

theorem jointHarm_hw_eq_bot : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    ¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s) = ⊥ :=
  fun _ _ _ _ μ μ' => (GlobalTheory.JointHarm.joint_harmonics μ μ').2

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOnTangentEqDerivativeBoundingFunctionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  first | exact @GlobalTheory.AnPer.LieVal.main | exact GlobalTheory.AnPer.LieVal.main | (intros; apply GlobalTheory.AnPer.LieVal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartNatMultipleEvalPropertiesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_natMultiple_eval_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n k, (∀ i, c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i)) ∧ (∀ f, c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f)) ∧ ∀ s, c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) := by
  first | exact @GlobalTheory.QLog.ChartMul.nmul_ev | exact GlobalTheory.QLog.ChartMul.nmul_ev | (intros; apply GlobalTheory.QLog.ChartMul.nmul_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneSubstOfEndomorphism
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobDefect

theorem hasSubst_cc {σ τ S : Type} [Finite σ] [CommRing S] {a : σ → MvPowerSeries τ S}
    (h : ∀ i, constantCoeff (a i) = 0) : HasSubst a := hasSubst_of_constantCoeff_zero h

theorem cc_map {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : MvPowerSeries σ R) :
    constantCoeff (map φ f) = φ (constantCoeff f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst (hasSubst_cc fun _ => constantCoeff_X _)]
  congr 1
  funext i
  simp

theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst (hasSubst_cc fun _ => constantCoeff_X _)]
  congr 1
  funext i
  simp

theorem mvPowerSeriesMap_evalTwoGroups {τ : Type} [Finite τ] (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]
  congr 1
  funext i
  cases i <;> rfl

theorem map_formalGroupLawCoboundaryOne_eq (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_cc hμ), map_inL, map_inR]

theorem formalGroupLawCoboundaryOne_sub (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) R) : cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  unfold cob1 inL inR
  rw [subst_sub (hasSubst_cc hμ), subst_sub (hasSubst_cc fun _ => constantCoeff_X _),
    subst_sub (hasSubst_cc fun _ => constantCoeff_X _)]
  abel

theorem powerSeriesEvalTwoGroups_sub {τ : Type} [Finite τ] (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : at2 (c - c') u v = at2 c u v - at2 c' u v := by
  unfold at2
  rw [subst_sub (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]

theorem formalGroupLawCoboundaryOne_subst_of_endomorphism (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (N : Fin d → MvPowerSeries (Fin d) R)
    (hN : ∀ i, constantCoeff (N i) = 0)
    (hom : ∀ j, subst μ (N j) = at2 (μ j) (fun i => inL (N i)) (fun i => inR (N i)))
    (f : MvPowerSeries (Fin d) R) :
    cob1 μ (subst N f) = at2 (cob1 μ f) (fun i => inL (N i)) (fun i => inR (N i)) := by
  have hL : ∀ i, constantCoeff (inL (N i)) = 0 := fun i => by
    unfold inL
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN i)
  have hR : ∀ i, constantCoeff (inR (N i)) = 0 := fun i => by
    unfold inR
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN i)
  have hE : HasSubst (Sum.elim (fun i => inL (N i)) (fun i => inR (N i))) :=
    hasSubst_cc fun i => by cases i <;> simp [hL, hR]
  have hXL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_cc fun _ => constantCoeff_X _
  have hXR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_cc fun _ => constantCoeff_X _
  have e1 : inL (subst N f) = subst (fun j => inL (N j)) f := by
    unfold inL
    rw [subst_comp_subst_apply (hasSubst_cc hN) hXL]
  have e2 : inR (subst N f) = subst (fun j => inR (N j)) f := by
    unfold inR
    rw [subst_comp_subst_apply (hasSubst_cc hN) hXR]
  have e3 : at2 (inL f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inL (N j)) f := by
    unfold at2
    rw [show inL f = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]
    rw [subst_comp_subst_apply hXL hE]
    congr 1
    funext j
    rw [subst_X hE]
    rfl
  have e4 : at2 (inR f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inR (N j)) f := by
    unfold at2
    rw [show inR f = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]
    rw [subst_comp_subst_apply hXR hE]
    congr 1
    funext j
    rw [subst_X hE]
    rfl
  have e5 : subst μ (subst N f) = at2 (subst μ f) (fun i => inL (N i)) (fun i => inR (N i)) := by
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_cc hN) (hasSubst_cc hμ),
      subst_comp_subst_apply (hasSubst_cc hμ) hE]
    congr 1
    funext j
    exact hom j
  unfold cob1
  rw [powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, e1, e2, e3, e4, e5]

theorem formalGroupLawCoboundaryOne_mulDefect (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ)
    (hinj : Function.Injective (algebraMap R Q)) (f : MvPowerSeries (Fin d) Q)
    (g : MvPowerSeries (Fin d ⊕ Fin d) R) (s : MvPowerSeries (Fin d) R) (k : ℕ)
    (hf : constantCoeff f = 0) (hg : map (algebraMap R Q) g = cob1 (up Q μ) f)
    (hs : map (algebraMap R Q) s = defect μ k f) :
    cob1 μ s = (k : R) • g - at2 g (fun i => inL (nmul μ k i)) (fun i => inR (nmul μ k i)) ∧
      constantCoeff g = 0 := by
  have hH := GlobalTheory.T.isHom_nmul_of_isLaw R d μ hμ k
  have hμ0 := hμ.const
  have hN0 := hH.const
  have hmapinj : ∀ {σ : Type} (a b : MvPowerSeries σ R),
      map (algebraMap R Q) a = map (algebraMap R Q) b → a = b := by
    intro σ a b h
    ext n
    apply hinj
    rw [← coeff_map, ← coeff_map, h]
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, cc_map, hμ0 i, map_zero]
  have hNQ : ∀ i, constantCoeff (up Q (nmul μ k) i) = 0 := fun i => by
    simp only [up, cc_map, hN0 i, map_zero]
  have hL : ∀ i, constantCoeff (inL (nmul μ k i)) = 0 := fun i => by
    unfold inL
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN0 i)
  have hR : ∀ i, constantCoeff (inR (nmul μ k i)) = 0 := fun i => by
    unfold inR
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN0 i)
  have homQ : ∀ j, subst (up Q μ) (up Q (nmul μ k) j) =
      at2 (up Q μ j) (fun i => inL (up Q (nmul μ k) i)) (fun i => inR (up Q (nmul μ k) i)) := by
    intro j
    have h1 := congrArg (map (algebraMap R Q)) (hH.hom j)
    rw [map_subst (hasSubst_cc hμ0)] at h1
    unfold pull2 at h1
    rw [mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR] at h1
    simp only [map_inL, map_inR] at h1
    exact h1
  constructor
  · apply hmapinj
    rw [map_formalGroupLawCoboundaryOne_eq _ _ hμ0, hs, map_sub, mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR]
    simp only [map_inL, map_inR]
    change cob1 (up Q μ) (defect μ k f) = _ - at2 _ (fun i => inL (up Q (nmul μ k) i))
      (fun i => inR (up Q (nmul μ k) i))
    rw [Nat.cast_smul_eq_nsmul R k g, map_nsmul, hg]
    unfold defect
    rw [formalGroupLawCoboundaryOne_sub _ hμQ, formalCoboundary_smul hμQ, Nat.cast_smul_eq_nsmul, formalGroupLawCoboundaryOne_subst_of_endomorphism _ hμQ _ hNQ homQ]
  · apply hinj
    rw [← cc_map, hg, map_zero]
    unfold cob1 inL inR
    rw [map_sub, map_sub, constantCoeff_subst_eq_zero (hasSubst_cc hμQ) hμQ hf,
      constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) hf,
      constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) hf]
    simp

theorem main : ∀ (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → Function.Injective (algebraMap R Q) → ∀ (f : MvPowerSeries (Fin d) Q) (g : MvPowerSeries (Fin d ⊕ Fin d) R) (s : MvPowerSeries (Fin d) R) (k : ℕ), constantCoeff f = 0 → map (algebraMap R Q) g = cob1 (up Q μ) f → map (algebraMap R Q) s = defect μ k f → cob1 μ s = (k : R) • g - at2 g (fun i => inL (nmul μ k i)) (fun i => inR (nmul μ k i)) ∧ constantCoeff g = 0 :=
  fun R Q _ _ _ d μ hμ hinj f g s k hf hg hs => formalGroupLawCoboundaryOne_mulDefect R Q d μ hμ hinj f g s k hf hg hs

end GlobalTheory.CobDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLawsStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧ nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧ (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i := by
  first | exact @GlobalTheory.NMul.nmul_laws | exact GlobalTheory.NMul.nmul_laws | (intros; apply GlobalTheory.NMul.nmul_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_strictHenselian_acyclic_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], SH A → AcycF R (sp B) F := by
  first | (exact @GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (exact GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (intros; apply GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral  <;> assumption)
end

