import Mathlib
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectors
section
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.GKLie

theorem epow_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) : ∀ k a b, R * epow E k a b = epow E' k a b * R := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [Formalism.REAL.epow]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    simp only [Formalism.REAL.epow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

theorem etr_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) (k : ℕ) : R * etr E k = etr E' k * R := by
  simp only [etr, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => epow_intertwine E E' R h k a a

theorem single_mul_single' {n : ℕ} (a b c d : Fin n) :
    (single a b (1 : ℂ)) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem conj_single {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * single a b 1 * P⁻¹ = ∑ c, ∑ d, (P c a * P⁻¹ b d) • single c d (1 : ℂ) := by
  ext i j
  simp [mul_apply, single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section Main

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem gAct_conj_glRel (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    GlRel (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) := by
  have hPi : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP)
  have hcb : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, P * X * P⁻¹ * (P * Y * P⁻¹) = P * (X * Y) * P⁻¹ := by
    intro X Y
    simp only [mul_assoc]
    rw [← mul_assoc P⁻¹ P, hPi, one_mul]
  intro a b c d
  simp only []
  rw [← gAct_bracket, hcb, hcb, ← sub_mul, ← mul_sub, single_mul_single', single_mul_single']
  split_ifs <;> simp [mul_sub, sub_mul]

theorem gAct_conj_sum (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) :
    (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) =
      fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • gAct hρ hV (single c d 1) := by
  funext a b
  rw [conj_single]
  simp only [map_sum, map_smul]

theorem gAct_conj_etr (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    etr (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) k = etr (fun a b => gAct hρ hV (single a b 1)) k := by
  rw [gAct_conj_sum]
  exact GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix (fun a b => gAct hρ hV (single a b 1)) P hP k

theorem dsigCW_eq (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (l : List (Fin n × Fin n)) (v : kFinVec ε ρ) :
    PI.DSInfCharCap.dsigCW ε ρ (l.map PI.DSInfCharCap.unitM) v =
      (((l.map fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)).prod v : kFinVec ε ρ) : H) := by
  induction l with
  | nil => simp [PI.DSInfCharCap.dsigCW]
  | cons x l ih =>
    rw [List.map_cons, PI.DSInfCharCap.dsigCW.eq_2, ih, List.map_cons, List.prod_cons, Module.End.mul_apply,
      gAct_coe]
    rfl

theorem actU_eq (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ) :
    actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)) p v :
      kFinVec ε ρ) : H) := by
  rw [GlobalTheory.T.freeAlgebra_lift_monoid_sum]
  unfold PI.DSInfCharCap.actU
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dsigCW_eq hρ hV]

end Main

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section KPart

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kset_facts {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) :
    κᴴ * κ = 1 ∧ κ⁻¹ = κᴴ ∧ κ * Jm ε = Jm ε * κ ∧ κᴴ * Jm ε = Jm ε * κᴴ := by
  obtain ⟨hu, hc⟩ := hκ
  have h1 : κᴴ * κ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hu
    simpa [Matrix.star_eq_conjTranspose] using hu
  refine ⟨h1, Matrix.inv_eq_left_inv h1, hc, ?_⟩
  have := congrArg conjTranspose hc
  simpa [conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem theta_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.thetaJ ε (κ * Y * κ⁻¹) = κ * PI.DSInfCharCap.thetaJ ε Y * κ⁻¹ := by
  obtain ⟨_, hinv, hc, hc'⟩ := kset_facts hκ
  rw [hinv]
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_mul, conjTranspose_conjTranspose, mul_neg, neg_mul, mul_assoc]
  rw [hc', ← mul_assoc (Jm ε) κ, ← hc, mul_assoc]

theorem cre_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cre ε (κ * Y * κ⁻¹) = κ * cre ε Y * κ⁻¹ := by
  unfold cre
  rw [theta_kconj hκ]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]

theorem cim_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cim ε (κ * Y * κ⁻¹) = κ * cim ε Y * κ⁻¹ := by
  unfold cim
  rw [theta_kconj hκ]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]

def kRes (hV : IsGKSub ε ρ (kFinVec ε ρ)) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε) :
    Module.End ℂ (kFinVec ε ρ) :=
  (ρ κ : H →ₗ[ℂ] H).restrict (fun x hx => hV.kStable κ hκ x hx)

theorem kRes_coe (hV : IsGKSub ε ρ (kFinVec ε ρ)) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε)
    (v : kFinVec ε ρ) : ((kRes hV κ hκ v : kFinVec ε ρ) : H) = ρ κ v := rfl

theorem gAct_kconj (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    kRes hV κ hκ * gAct hρ hV Y = gAct hρ hV (κ * Y * κ⁻¹) * kRes hV κ hκ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, kRes_coe, gAct_coe, gAct_coe, kRes_coe, dsigC_eq, dsigC_eq,
    cre_kconj hκ, cim_kconj hκ,
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cre_mem Y) v (hV.smooth v v.2),
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cim_mem Y) v (hV.smooth v v.2), map_add, map_smul]

theorem etr_kequiv (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (k : ℕ) (v w : kFinVec ε ρ) (hw : (w : H) = ρ κ v) :
    ((etr (fun a b => gAct hρ hV (single a b 1)) k w : kFinVec ε ρ) : H) =
      ρ κ ((etr (fun a b => gAct hρ hV (single a b 1)) k v : kFinVec ε ρ) : H) := by
  have hw' : w = kRes hV κ hκ v := Subtype.ext (by rw [hw, kRes_coe])
  have hU : IsUnit κ := (isUnit_iff_isUnit_det κ).2 (isUnit_det_of_left_inverse (kset_facts hκ).1)
  have hint := etr_intertwine (fun a b => gAct hρ hV (single a b 1))
    (fun a b => gAct hρ hV (κ * single a b 1 * κ⁻¹)) (kRes hV κ hκ) (fun a b => gAct_kconj hρ hV hκ _) k
  rw [gAct_conj_etr hρ hV κ hU k] at hint
  rw [hw', ← kRes_coe hV κ hκ, ← Module.End.mul_apply, ← Module.End.mul_apply, hint]

theorem eword_coef (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (w' : H) :
    ∀ (l : List (Fin n × Fin n)) (u : kFinVec ε ρ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Eword ε l (fun x => ⟪w', ρ x u⟫_ℂ) g =
        ⟪w', ρ g (((l.map fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)).prod u : kFinVec ε ρ) : H)⟫_ℂ := by
  intro l
  induction l with
  | nil => intro u g _; simp [Formalism.REAL.Eword]
  | cons p l ih =>
    intro u g hg
    rw [Formalism.REAL.Eword.eq_2]
    beta_reduce
    rw [GlobalTheory.T.matrix_coefficient_derivative_formula n ε H ρ hρ _ (hV.smooth _ ((l.map fun ab : Fin n × Fin n =>
      gAct hρ hV (single ab.1 ab.2 1)).prod u).2) w' _ (fun g' hg' => ih u g' hg') p.1 p.2 g hg]
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, gAct_coe]

theorem gelf_coef (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (w' : H) (m : ℕ)
    (v : kFinVec ε ρ) :
    GlobalTheory.Dec.gelf ε m (fun x => ⟪w', ρ x v⟫_ℂ) 1 =
      ⟪w', ((etr (fun a b => gAct hρ hV (single a b 1)) (m + 1) v : kFinVec ε ρ) : H)⟫_ℂ := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [Formalism.REAL.inUJ]
  unfold GlobalTheory.Dec.gelf
  rw [GlobalTheory.T.elementary_trace_power_cyclic_words]
  simp only [eword_coef hρ hV w' _ v 1 h1, hρ.1, ContinuousLinearMap.one_apply, LinearMap.sum_apply,
    Submodule.coe_sum, inner_sum]

theorem etr_infChar (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (χ : Fin n → ℂ)
    (hχ : HasInfChar ε χ ρ) (k : ℕ) (v : kFinVec ε ρ) :
    etr (fun a b => gAct hρ hV (single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  set T := etr (fun a b => gAct hρ hV (single a b 1)) (k + 1) with hT
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [Formalism.REAL.inUJ]
  have key : ∀ w' : kFinVec ε ρ, ⟪(w' : H), (T v : H)⟫_ℂ = gelfVal χ (k + 1) * ⟪(w' : H), (v : H)⟫_ℂ := by
    intro w'
    have := (hχ v w' v.2 w'.2).2 k 1 h1
    rw [gelf_coef hρ hV] at this
    simpa [hρ.1] using this
  set z : kFinVec ε ρ := T v - gelfVal χ (k + 1) • v with hz
  have hzH : (z : H) = (T v : H) - gelfVal χ (k + 1) • (v : H) := by
    rw [hz, Submodule.coe_sub, Submodule.coe_smul]
  have hzz : ⟪(z : H), (z : H)⟫_ℂ = 0 := by
    conv_lhs => arg 3; rw [hzH]
    rw [inner_sub_right, inner_smul_right, key z, sub_self]
  have h0 : (z : H) = 0 := inner_self_eq_zero.1 hzz
  exact sub_eq_zero.1 (Subtype.ext h0)

end KPart

theorem kFin_glModule : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → IsGKSub ε ρ (kFinVec ε ρ) → ∃ A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (kFinVec ε ρ), (∀ X ∈ lieSet ε, ∀ v, ((A X v : kFinVec ε ρ) : H) = dRep ρ X v) ∧ (∀ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P → GlRel (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) ∧ ∀ k : ℕ, etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) k = etr (fun a b => A (Matrix.single a b 1)) k) ∧ (∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ), actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1)) p v : kFinVec ε ρ) : H)) ∧ (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((etr (fun a b => A (Matrix.single a b 1)) k w : kFinVec ε ρ) : H) = ρ κ ((etr (fun a b => A (Matrix.single a b 1)) k v : kFinVec ε ρ) : H)) ∧ ∀ χ : Fin n → ℂ, HasInfChar ε χ ρ → ∀ (k : ℕ) v, etr (fun a b => A (Matrix.single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  intro n ε H _ _ _ ρ hadm hV
  have hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ := hadm.1
  exact ⟨gAct hρ hV, fun X hX v => gAct_of_mem hρ hV hX v,
    fun P hP => ⟨gAct_conj_glRel hρ hV P hP, gAct_conj_etr hρ hV P hP⟩, fun p v => actU_eq hρ hV p v,
    fun κ hκ k v w hw => etr_kequiv hρ hV hκ k v w hw, fun χ hχ k v => etr_infChar hρ hV χ hχ k v⟩

end GlobalTheory.GKLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfAdelicHomDecomposeIsotropicMiddleComplement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem adj_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) (B : Matrix (Fin b) (Fin c) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) : adj D (adj D A) = A := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_one {a : ℕ} : adj D (1 : Matrix (Fin a) (Fin a) D.host.E) = 1 := by
  simp [adj, Formalism.UG.cT]

theorem adj_zero {a b : ℕ} : adj D (0 : Matrix (Fin a) (Fin b) D.host.E) = 0 := by
  simp [adj, Formalism.UG.cT]

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem exists_decomp_one (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B)
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (hKC : K * C = 1) (hKB : K * B = 0) :
    ∃ N' : Matrix (Fin V.rank) (Fin r) D.host.E,
      C * K + (B * (V'.gram⁻¹ * adj D B * V.gram) + N' * (adj D C * V.gram)) = 1 := by
  set G := V.gram
  set Pi := adj D C * G
  set Pm := V'.gram⁻¹ * adj D B * G
  set N := G⁻¹ * adj D K
  set N' := N - C * (K * N) - B * (Pm * N)
  have hG := GlobalTheory.LatVac.gram_det_isUnit V
  have hG' := GlobalTheory.LatVac.gram_det_isUnit V'
  have hPiC : Pi * C = 0 := hs.frame.2.2
  have hPiB : Pi * B = 0 := hs.orth
  have hBC : adj D B * G * C = 0 := by
    have h := congrArg (adj D) hs.orth
    rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero, ← Matrix.mul_assoc] at h
    exact h
  have hPmC : Pm * C = 0 := by
    simp only [Pm, Matrix.mul_assoc] at hBC ⊢
    rw [hBC, Matrix.mul_zero]
  have hPmB : Pm * B = 1 := by
    simp only [Pm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (adj D B), hs.isom, Matrix.nonsing_inv_mul _ hG']
  have hPiN : Pi * N = 1 := by
    simp only [Pi, N, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, ← adj_mul, hKC, adj_one]
  have hKN' : K * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hKC, hKB, Matrix.one_mul, Matrix.zero_mul, sub_self, sub_zero]
  have hPmN' : Pm * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPmC, hPmB, Matrix.one_mul, Matrix.zero_mul, sub_zero, sub_self]
  have hPiN' : Pi * N' = 1 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPiC, hPiB, Matrix.zero_mul, sub_zero]
    simpa only [Pi, N, Matrix.mul_assoc] using hPiN
  let M : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows K (Matrix.fromRows Pm Pi)
  let Q : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E :=
    Matrix.fromCols C (Matrix.fromCols B N')
  have hMQ : M * Q = 1 := by
    simp only [M, Q, Matrix.fromRows_mul, Matrix.mul_fromCols, hKC, hKB, hKN', hPmC, hPmB, hPmN', hPiC, hPiB, hPiN']
    refine Matrix.ext fun a b => ?_
    rcases a with a | a | a <;> rcases b with b | b | b <;> simp [Matrix.one_apply]
  have e : Fin r ⊕ (Fin V'.rank ⊕ Fin r) ≃ Fin V.rank :=
    Fintype.equivOfCardEq (by simp [hs.rank]; ring)
  have hQM : Q * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hMQ
  refine ⟨N', ?_⟩
  simpa only [M, Q, Matrix.fromCols_mul_fromRows] using hQM

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

theorem half_decomp : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ (a : AE D) (u : WO V W), IsHalf a u → ∃ (y : Mx D W.rank r) (x : WO V' W) (t : Mx D W.rank r), IsHalf a y ∧ IsHalf a x ∧ IsHalf a t ∧ u = isoPart V W C y + midPart V V' W B x + restEmb V W K t := by
  intro D V V' W r C B hs K hKC hKB a u hu
  obtain ⟨N', hN'⟩ := exists_decomp_one V V' C B hs K hKC hKB
  refine ⟨HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (N'.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (B.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (C.map (incA D)),
    isHalf_mul hu _, isHalf_mul hu _, isHalf_mul hu _, ?_⟩
  have h1 := congrArg (fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (incA D)) hN'
  simp only [Matrix.map_add, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [isoPart, midPart, restEmb, Matrix.map_mul, Matrix.mul_assoc]
  conv_lhs => rw [← Matrix.mul_one u, ← h1]
  simp only [Matrix.map_add _ (map_add (incA D)), Matrix.map_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

end GlobalTheory.HalfDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtLevelIndicatorCoefficientTestOneParam
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TermDeriv

theorem hasDerivAt_coef_oneP : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  intro D hHC θ hθ V S M K v b τ hb X hX x
  have hfin : ∀ s : ℝ, Lev.finE V (x * oneP θ V τ X s) = Lev.finE V x := by
    intro s
    have h : finHom V (oneP θ V τ X s) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
    show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X s) = _
    rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X s), h, map_one, mul_one]
    rfl
  by_cases hK : Lev.finE V x ∈ K
  swap
  · have e : (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun _ => 0 := by
      funext s
      simp only [coef, hfin s, hK, if_false]
    rw [e]
    have e2 : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x = 0 := by
      simp only [coef, hK, if_false]
    rw [e2]
    exact hasDerivAt_const _ _
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hsv : SmoothVec (lieAt V τ) (M.rep τ) (b τ) :=
    hHC.smoothVec hstd.1 hstd.2.1 hb (M.fr_unit τ) (M.fr_gram τ)
  have hd0 := Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_hasDerivAt hsv hX 0
  rw [zero_smul, NormedSpace.exp_zero, Formalism.IndefR.SchurOrthogonalityAlt.gp_rep_one, ContinuousLinearMap.one_apply] at hd0
  set c : ℂ := ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' x) (b τ')⟫_ℂ with hc
  have hfun : ∀ s : ℝ, coef θ M K v b (x * oneP θ V τ X s) =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ := by
    intro s
    simp only [coef, hfin s, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
    congr 1
    · refine Finset.prod_congr rfl fun τ' hτ' => ?_
      have hne := Finset.ne_of_mem_erase hτ'
      have h := (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.2 τ' hne
      show ⟪v τ', M.rep τ' (infMat D.sp.cm.sig V.gram (θ τ') (x * oneP θ V τ X s)) (b τ')⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, h, Matrix.mul_one]
    · show ⟪v τ, M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (x * oneP θ V τ X s)) (b τ)⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.1,
        Formalism.IndefR.SchurOrthogonalityAlt.rep_mul M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ) (GlobalTheory.Mem.Lift.exp_mem hX s)]
      rfl
  have hval : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (dRep (M.rep τ) X (b τ))⟫_ℂ := by
    simp only [coef, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun τ' hτ' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ')]
  rw [hval, show (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun s : ℝ =>
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ from funext hfun]
  refine HasDerivAt.const_mul c ?_
  exact (((innerSL ℂ (v τ)).comp (M.rep τ (cmp θ τ x))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd0

end GlobalTheory.TermDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory

theorem hasSum_pow_div_factorial_exp (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

theorem hasSum_fin_prod_pow_div_factorial_exp : ∀ (n : ℕ) (x : Fin n → ℂ),
    HasSum (fun f : Fin n → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro n
  induction n with
  | zero =>
    intro x
    have := hasSum_unique (fun f : Fin 0 → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
    simpa using this
  | succ n ih =>
    intro x
    have h := hasSum_pow_div_factorial_exp (x 0)
    have ht := ih (Fin.tail x)
    have h1 : Summable (fun i => ‖x 0 ^ i / (i.factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 h.summable
    have h2 : Summable (fun f : Fin n → ℕ => ‖∏ k, Fin.tail x k ^ f k / ((f k).factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 ht.summable
    have h0 := summable_mul_of_summable_norm h1 h2
    have h3 := HasSum.mul h ht h0
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff, Fin.sum_univ_succ,
      Complex.exp_add]
    convert h3 using 1
    all_goals first
      | rfl
      | (funext p; simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail] <;> ring)

theorem hasSum_finsupp_prod_pow_div_factorial_exp : ∀ (κ : Type) [Fintype κ] (x : κ → ℂ),
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro κ _ x
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hA := hasSum_fin_prod_pow_div_factorial_exp (Fintype.card κ) (fun i => x (e.symm i))
  have hsum : (∑ i, x (e.symm i)) = ∑ k, x k := Equiv.sum_comp e.symm x
  rw [hsum] at hA
  have hB : HasSum (fun f : κ → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
    rw [← ((Equiv.arrowCongr e (Equiv.refl ℕ)).symm).hasSum_iff]
    convert hA using 1
    funext g
    simp only [Function.comp_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
      Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, Function.comp_def, id]
    exact (Equiv.prod_comp e.symm (fun k => x k ^ g (e k) / ((g (e k)).factorial : ℂ))).symm.trans
      (by simp)
  rw [← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).symm.hasSum_iff]
  convert hB using 1
  funext f
  simp only [Function.comp_apply]
  rw [Finsupp.prod_fintype]
  · simp
  · intro i; simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSkewAdjoint_mem_adjoint_homLattice : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  first | exact @GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | exact GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | (intros; apply GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO <;> assumption)
end

