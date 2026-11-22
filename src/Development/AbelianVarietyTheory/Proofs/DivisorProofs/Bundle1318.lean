import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTorsionPointsStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_off_diagonal_block : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η := by
  first | exact @GlobalTheory.CurvSQ.blockSQ_curv_eq_covDelAnti_extForm | exact GlobalTheory.CurvSQ.blockSQ_curv_eq_covDelAnti_extForm | (intros; apply GlobalTheory.CurvSQ.blockSQ_curv_eq_covDelAnti_extForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRangeOfSteps
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWWeil

open GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

abbrev unipN (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) : Subgroup (UA σ J₂) :=
  unipOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype

abbrev ratN (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) : Subgroup (unipN σ J₂) :=
  (ratU σ J₂).comap (unipN σ J₂).subtype

def IsRatChar {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (lam : unipN σ J₂ →* Circle) : Prop :=
  Continuous (fun x => (lam x : ℂ)) ∧ ∀ x ∈ ratN σ J₂, lam x = 1

def coefN {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂))
    (lam : unipN σ J₂ →* Circle) (A : UA σ J₂ → ℂ) (g : UA σ J₂) : ℂ :=
  ⨍ x in 𝓓, A ((x : UA σ J₂) * g) * (starRingEnd ℂ) (lam x : ℂ) ∂νN

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type}

def eisW (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : ℂ :=
  GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂) (fun x => om (1, x) Φ 0) g

def thetaI [Fintype κ] (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) (ν : Measure (UA σ JV))
    (𝓕 : Set (UA σ JV)) (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : ℂ :=
  ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν

end GlobalTheory.SWWeil

namespace GlobalTheory.SWWeil
open GlobalTheory.SWLit GlobalTheory.SWACase

def StepConv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) (eisW σ om Φ g)

def StepReg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  (∀ g, Continuous fun x : unipN σ J₂ => eisW σ om Φ ((x : UA σ J₂) * g) - thetaI σ om ν 𝓕 Φ ((x : UA σ J₂) * g)) ∧
  ∀ x ∈ ratN σ J₂, ∀ g, eisW σ om Φ ((x : UA σ J₂) * g) - thetaI σ om ν 𝓕 Φ ((x : UA σ J₂) * g) =
    eisW σ om Φ g - thetaI σ om ν 𝓕 Φ g

def StepCoef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam →
  ∀ g, coefN σ νN 𝓓 lam (fun x => eisW σ om Φ x - thetaI σ om ν 𝓕 Φ x) g = 0

def StepUniq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (n : ℕ), 1 ≤ n →
  ∀ (l : E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∃ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure ∧ IsFundamentalDomain (ratN σ J₂) 𝓓 νN ∧
    ∀ A : UA σ J₂ → ℂ, (∀ g, Continuous fun x : unipN σ J₂ => A ((x : UA σ J₂) * g)) →
      (∀ x ∈ ratN σ J₂, ∀ g, A ((x : UA σ J₂) * g) = A g) →
      (∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam → ∀ g, coefN σ νN 𝓓 lam A g = 0) → ∀ g, A g = 0

end GlobalTheory.SWWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylFormulaCompactTorusIdentityOfIngredients
section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.HCChar (dsChar)

namespace GlobalTheory.PsCo.PcEF

namespace WeylCompactTorusIdentity

theorem alg {W S C M s p x : ℂ} (hs : s * s = 1) (hp : p * p = 1) (hW : W ≠ 0) (hM : M ≠ 0) (hs0 : s ≠ 0)
    (hx : W * x = S * C) : s * x = p * S / (W * (s * M)) * (p * M * C) := by
  have hden : W * (s * M) ≠ 0 := mul_ne_zero hW (mul_ne_zero hs0 hM)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (M * s * s) * hx + (M * S * C) * hs - (M * S * C) * hp

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem prod_tor_pow_eq_wtVal_mul {n : ℕ} (lam : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) (θ : Fin n → ℝ) (w : Equiv.Perm (Fin n)) :
    ∏ a, tor θ a ^ m (w.symm a) =
      GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ * GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ := by
  show ∏ a, Complex.exp (↑(θ a) * Complex.I) ^ m (w.symm a) = _
  unfold GlobalTheory.HCChar.wtVal
  rw [← Complex.exp_add]
  rw [Finset.prod_congr rfl (fun a _ => (Complex.exp_int_mul (↑(θ a) * Complex.I) (m (w.symm a))).symm),
    ← Complex.exp_sum]
  congr 1
  push_cast
  rw [← add_mul, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h2 : ((m (w.symm a) : ℤ) : ℂ) = ((lam (w.symm a) : ℝ) : ℂ) + ((n : ℂ) - 1) / 2 := by
    have h3 := congrArg (fun r : ℝ => (r : ℂ)) (hm (w.symm a))
    push_cast at h3
    exact h3.symm
  simp only [h2, Function.comp_apply]
  ring

end WeylCompactTorusIdentity

open WeylCompactTorusIdentity in

theorem weylFormulaCompactTorusIdentity_of_ingredients : VdmSplit → PhysTor → NumShift → TorusId := by
  intro hV hP hN n ε lam Λ m hm hΛ θ hinj x hx
  have ht0 : ∀ a, tor θ a ≠ 0 := fun a => Complex.exp_ne_zero _
  obtain ⟨hPD, -⟩ := hP n ε θ
  have hVd := hV n ε (tor θ)
  have hWd : GlobalTheory.HCChar.weylDenom θ * GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ =
      ∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b) := GlobalTheory.HCChar.weylDenom_mul θ
  have hNum : (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
      ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, tor θ a ^ m (w.symm a)) =
      (∑ w ∈ GlobalTheory.HCChar.compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ) *
        GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [prod_tor_pow_eq_wtVal_mul lam m hm θ w]
    ring
  have hx' : ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x =
      ((∑ w ∈ GlobalTheory.HCChar.compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ) *
        GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) := by
    rw [hx, ← hNum]
    exact (congrArg (fun μ => ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε μ (tor θ)) (funext hΛ)).trans
      (hN n ε m (fun b : Bool => if b then (0 : ℤ) else (pOf ε : ℤ)) (tor θ) ht0)
  have hV0 : (∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
    exact sub_ne_zero.mpr (fun h => (Finset.mem_Ioi.mp hb).ne (hinj h))
  rw [hVd] at hV0
  have hW0 := left_ne_zero_of_mul hV0
  have hPm0 := right_ne_zero_of_mul (right_ne_zero_of_mul hV0)
  have hh : GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ ≠ 0 := Complex.exp_ne_zero _
  have key := alg (s := (-1) ^ sDeg ε) (p := (-1) ^ (pOf ε * qOf ε)) (neg_one_pow_mul_self _)
    (neg_one_pow_mul_self _) hW0 hPm0 (pow_ne_zero _ (by norm_num)) hx'
  rw [key, hPD, ← hVd, ← hWd]
  unfold GlobalTheory.HCChar.dsChar
  congr 1
  rw [← mul_assoc, mul_div_mul_right _ _ hh]
  try rfl

end GlobalTheory.PsCo.PcEF

end
end

namespace GlobalTheory.PsCo.PcEF
open GlobalTheory.PsCo.PcEG

theorem torusId_full : TorusId := weylFormulaCompactTorusIdentity_of_ingredients vandermonde_splits_compactNoncompact adjointDet_onCompactTorus numShift_holds

end GlobalTheory.PsCo.PcEF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInv
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrame

theorem yx_eq_one : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) * X = 1 := by
  intro D V r X Y hW
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  have hX : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X) = X := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, star_star]
  have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) hW.xy
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJ, Formalism.UG.cT_one] at h
  rwa [Matrix.mul_assoc]

end GlobalTheory.WittFrame
end

