import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0188
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixClosedDerivLinearAdd
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwartzDeriv

section General

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]

theorem addHom_eq_zero (F : Type) [DivisionRing F] [CharZero F] [Module F X] (h : ℝ →+ X) (hc : Continuous h) {b : ℝ}
    (hb : b ≠ 0) (h0 : h b = 0) (t : ℝ) : h t = 0 := by

  have hq : ∀ q : ℚ, h ((q : ℝ) * b) = 0 := by
    intro q
    have hn : (q.den : F) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hnum : (q.den : ℝ) * ((q : ℝ) * b) = (q.num : ℝ) * b := by
      rw [← mul_assoc]
      congr 1
      have : ((q.den : ℚ) * q : ℚ) = q.num := by rw [mul_comm]; exact Rat.mul_den_eq_num q
      exact_mod_cast this
    have h1 : q.den • h ((q : ℝ) * b) = 0 := by
      rw [← map_nsmul, nsmul_eq_mul, hnum, ← zsmul_eq_mul, map_zsmul, h0, smul_zero]
    have h2 : h ((q : ℝ) * b) = (q.den : F)⁻¹ • ((q.den : F) • h ((q : ℝ) * b)) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [h2, Nat.cast_smul_eq_nsmul, h1, smul_zero]
  have hsurj : Function.Surjective fun y : ℝ => y * b := fun y => ⟨y / b, div_mul_cancel₀ y hb⟩
  have hdense : DenseRange fun q : ℚ => (q : ℝ) * b :=
    hsurj.denseRange.comp Rat.denseRange_cast (continuous_mul_const b)
  exact hdense.induction_on t (isClosed_eq hc continuous_const) hq

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : SchwartzMap E ℂ) (c s : E) :
    HasDerivAt (fun t : ℝ => G (s + t • c)) ((LineDeriv.lineDerivOp c G : SchwartzMap E ℂ) s) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => s + t • c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add s
  have h2 : HasFDerivAt (G : E → ℂ) (fderiv ℝ (G : E → ℂ) (s + (0 : ℝ) • c)) (s + (0 : ℝ) • c) :=
    G.differentiableAt.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero] at h3
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact h3

theorem exists_schwartz_deriv (F : Type) [DivisionRing F] [CharZero F] [Module F X] (P : X → Prop)
    (hP : ∀ a b, P a → P b → P (a + b)) (φ : X → ℂ)
    (hφ : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ X), (Continuous L ∧ ∀ t, P (L t)) → Function.Injective L →
      ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t))
    (M : ℝ →+ X) (hM : Continuous M) (hMP : ∀ t, P (M t)) {k : ℕ} (L : (Fin k → ℝ) →+ X)
    (hL : Continuous L ∧ ∀ t, P (L t)) (hi : Function.Injective L) (x : X) :
    ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ s, HasDerivAt (fun t : ℝ => φ (x + L s + M t)) (g s) 0 := by
  obtain ⟨hLc, hLP⟩ := hL

  let A : (Fin (k + 1) → ℝ) →+ (Fin k → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (Fin.castSucc : Fin k → Fin (k + 1))).toAddMonoidHom
  let B : (Fin (k + 1) → ℝ) →+ ℝ := Pi.evalAddMonoidHom (fun _ => ℝ) (Fin.last k)
  let L' : (Fin (k + 1) → ℝ) →+ X := L.comp A + M.comp B
  have hA : Continuous A := continuous_pi fun i => continuous_apply _
  have hB : Continuous B := continuous_apply _
  have hL'c : Continuous L' := (hLc.comp hA).add (hM.comp hB)
  have hL'P : ∀ u, P (L' u) := fun u => hP _ _ (hLP _) (hMP _)
  have hL'apply : ∀ u, L' u = L (fun i => u (Fin.castSucc i)) + M (u (Fin.last k)) := fun u => rfl
  by_cases hinj : Function.Injective L'
  ·
    obtain ⟨H, hH⟩ := hφ (k + 1) L' ⟨hL'c, hL'P⟩ hinj x
    let e : Fin (k + 1) → ℝ := Pi.single (Fin.last k) 1
    let j : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
      ContinuousLinearMap.pi (Fin.lastCases (motive := fun _ => (Fin k → ℝ) →L[ℝ] ℝ) 0
        fun i => ContinuousLinearMap.proj i)
    have hj_cs : ∀ s i, j s (Fin.castSucc i) = s i := by intro s i; simp [j]
    have hj_last : ∀ s, j s (Fin.last k) = 0 := by intro s; simp [j]
    have hup : ∃ (n : ℕ) (C : ℝ), ∀ s, ‖s‖ ≤ C * (1 + ‖j s‖) ^ n := by
      refine ⟨1, 1, fun s => ?_⟩
      rw [one_mul, pow_one]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      calc ‖s i‖ = ‖j s (Fin.castSucc i)‖ := by rw [hj_cs]
        _ ≤ ‖j s‖ := norm_le_pi_norm _ _
        _ ≤ 1 + ‖j s‖ := by linarith
    refine ⟨SchwartzMap.compCLM ℝ j.hasTemperateGrowth hup (LineDeriv.lineDerivOp e H), fun s => ?_⟩
    have hd := hasDerivAt_line H e (j s)
    have heq : (fun t : ℝ => H (j s + t • e)) = fun t => φ (x + L s + M t) := by
      funext t
      have e1 : (fun i => (j s + t • e) (Fin.castSucc i)) = s := by
        funext i
        simp [e, hj_cs, Fin.castSucc_ne_last]
      have e2 : (j s + t • e) (Fin.last k) = t := by simp [e, hj_last]
      rw [hH, hL'apply, e1, e2, add_assoc]
    rw [heq] at hd
    exact hd
  ·
    obtain ⟨u, hu, hu0⟩ : ∃ u, L' u = 0 ∧ u ≠ 0 := by
      rw [injective_iff_map_eq_zero] at hinj
      push Not at hinj
      exact hinj
    rw [hL'apply] at hu
    have ht0 : u (Fin.last k) ≠ 0 := by
      intro h
      rw [h, map_zero, add_zero] at hu
      have hs : (fun i => u (Fin.castSucc i)) = 0 := hi (by rw [hu, map_zero])
      apply hu0
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact h
      · exact congrFun hs i
    let v : Fin k → ℝ := -((u (Fin.last k))⁻¹ • fun i => u (Fin.castSucc i))
    let Lv : ℝ →+ (Fin k → ℝ) := AddMonoidHom.mk' (fun t => t • v) fun a b => add_smul a b v
    have hMv : ∀ t, M t = L (t • v) := by
      intro t
      have h1 := addHom_eq_zero F (M - L.comp Lv)
        (hM.sub (hLc.comp (continuous_id.smul continuous_const))) ht0 ?_ t
      · simpa [sub_eq_zero, Lv] using h1
      · simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, Lv, v, smul_neg,
          smul_smul, mul_inv_cancel₀ ht0, one_smul, map_neg, sub_neg_eq_add]
        rw [add_comm]
        exact hu
    obtain ⟨G, hG⟩ := hφ k L ⟨hLc, hLP⟩ hi x
    refine ⟨LineDeriv.lineDerivOp v G, fun s => ?_⟩
    have hd := hasDerivAt_line G v s
    have heq : (fun t : ℝ => G (s + t • v)) = fun t => φ (x + L s + M t) := by
      funext t
      rw [hG, hMv, map_add, add_assoc]
    rw [heq] at hd
    exact hd

end General

open GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7} {m n : ℕ}

theorem isSchwartzBruhat_add {φ φ' : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (h' : IsSchwartzBruhat φ') :
    IsSchwartzBruhat (φ + φ') where
  level := by
    obtain ⟨U, hU, hφU⟩ := h.level
    obtain ⟨U', hU', hφU'⟩ := h'.level
    refine ⟨U ⊓ U', by simpa [AddSubgroup.coe_inf] using hU.inter hU', fun u hu hu0 x => ?_⟩
    have hu' := AddSubgroup.mem_inf.mp hu
    simp [hφU u hu'.1 hu0 x, hφU' u hu'.2 hu0 x]
  supp := by
    obtain ⟨K, hK, hφK⟩ := h.supp
    obtain ⟨K', hK', hφK'⟩ := h'.supp
    refine ⟨K ∪ K', hK.union hK', fun x hx => ?_⟩
    by_cases h1 : φ x = 0
    · have h2 : φ' x ≠ 0 := by simpa [h1] using hx
      exact Or.inr (hφK' x h2)
    · exact Or.inl (hφK x h1)
  schwartz := by
    intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x
    obtain ⟨g', hg'⟩ := h'.schwartz k L hL hi x
    exact ⟨g + g', fun t => by simp [hg, hg']⟩

theorem isSchwartzBruhat_linear_mul {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (ℓ : Mx D m n →+ ℂ) (hc : Continuous ℓ)
    (h0 : ∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) : IsSchwartzBruhat fun x => ℓ x * φ x where
  level := by
    obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    show ℓ (x + u) * φ (x + u) = ℓ x * φ x
    rw [map_add, h0 u hu0, add_zero, hφU u hu hu0 x]
  supp := by
    obtain ⟨K, hK, hφK⟩ := h.supp
    exact ⟨K, hK, fun x hx => hφK x (right_ne_zero_of_mul hx)⟩
  schwartz := by
    intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x

    let A : (Fin k → ℝ) →L[ℝ] ℂ := (ℓ.comp L).toRealLinearMap (hc.comp hL.1)
    have ht : (fun t => ℓ x + A t).HasTemperateGrowth := by fun_prop
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun t => ℓ x + A t) g, fun t => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply ht, hg]
    simp [A, smul_eq_mul]

theorem exists_isSchwartzBruhat_deriv {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (M : ℝ →+ Mx D m n) (hM : Continuous M)
    (hM0 : ∀ t, (M t).map (finPart D) = 0) :
    ∃ φ', IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0 := by
  have : T2Space (Mx D m n) := (lattice_Mx D m n).2.2.2.1
  have hP : ∀ a b : Mx D m n, a.map (finPart D) = 0 → b.map (finPart D) = 0 → (a + b).map (finPart D) = 0 := by
    intro a b ha hb
    rw [Matrix.map_add _ (map_add _), ha, hb, add_zero]

  have hdiff : ∀ y, HasDerivAt (fun t : ℝ => φ (y + M t)) (deriv (fun t : ℝ => φ (y + M t)) 0) 0 := by
    intro y
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 (k := 0) 0 ⟨continuous_const, fun t => by simp⟩ (fun a b _ => Subsingleton.elim a b) y
    have hg0 := hg 0
    simp only [AddMonoidHom.zero_apply, add_zero] at hg0
    exact hg0.differentiableAt.hasDerivAt
  refine ⟨fun x => deriv (fun t : ℝ => φ (x + M t)) 0, ⟨?_, ?_, ?_⟩, hdiff⟩
  · obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    simp only [add_right_comm x u, hφU u hu hu0]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    refine ⟨K, hK, fun x hx => ?_⟩
    by_contra hxK
    apply hx
    have hz : (fun t : ℝ => φ (x + M t)) = fun _ => 0 := by
      funext t
      by_contra ht
      apply hxK
      have := hφK _ ht
      rwa [Matrix.map_add _ (map_add _), hM0, add_zero] at this
    simp only [hz, deriv_const]
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 L hL hi x
    exact ⟨g, fun s => (hg s).deriv.symm⟩

theorem isSchwartzBruhat_closed : ∀ (D : D7) (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → (∀ M : ℝ →+ Mx D m n, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0) ∧ (∀ ℓ : Mx D m n →+ ℂ, Continuous ℓ → (∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat fun x => ℓ x * φ x) ∧ ∀ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (φ + φ') := fun _ _ _ _ hφ =>
  ⟨fun M hM hM0 => exists_isSchwartzBruhat_deriv hφ M hM hM0, fun ℓ hc h0 => isSchwartzBruhat_linear_mul hφ ℓ hc h0,
    fun _ h' => isSchwartzBruhat_add hφ h'⟩

end GlobalTheory.SchwartzDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplexStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_isotropic_columns_ring_iso_complex : ∀ {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ), Function.Bijective f → (∀ x, f (σ x) = star (f x)) → ∀ {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool), Formalism.UG.cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1) → ∀ (X : Matrix (Fin n) (Fin r) A), Formalism.UG.cT σ X * J * X = 0 → ∀ g : GL (Fin n) A, g ∈ UJ σ J → ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧ ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β := by
  first | exact @GlobalTheory.Core.Rk.IwArch.iw_iso_cols | exact GlobalTheory.Core.Rk.IwArch.iw_iso_cols | (intros; apply GlobalTheory.Core.Rk.IwArch.iw_iso_cols <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteTranslatesFiniteDimensionalStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K_finite_translates_finite_dimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ φ, IsKFinVec omh (Khat A a) φ → ∀ K : Set (GA D A), IsCompact K → FiniteDimensional ℂ (Submodule.span ℂ {f : WO (dblSp A) W → ℂ | ∃ g₁ ∈ K, ∃ g₂ ∈ K, f = omh (io A (g₁, g₂), 1) φ}) := by
  first | exact @GlobalTheory.Core.Rk.FinDim.finiteDimensional_span_io | exact GlobalTheory.Core.Rk.FinDim.finiteDimensional_span_io | (intros; apply GlobalTheory.Core.Rk.FinDim.finiteDimensional_span_io <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KeepsDiagOfMulStkRowsOne
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SW

theorem keepsDiag_of_mul_stkRows_one {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    {β : Matrix (Fin n) (Fin n) R} (h : M * stkRows 1 1 = stkRows β β) : KeepsDiag finSumFinEquiv M := by
  rw [keepsDiag_iff]
  have key : ∀ s : Fin n ⊕ Fin n, ∀ j, M (finSumFinEquiv s) (finSumFinEquiv (Sum.inl j)) +
      M (finSumFinEquiv s) (finSumFinEquiv (Sum.inr j)) = β (s.elim id id) j := by
    intro s j
    have h1 : ∑ k, M (finSumFinEquiv s) k * stkRows (1 : Matrix (Fin n) (Fin n) R) 1 k j =
        stkRows β β (finSumFinEquiv s) j := congrFun (congrFun h _) j
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at h1
    simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    rw [h1]
    rcases s with s | s <;> rfl
  intro i j
  rw [key (Sum.inr i), key (Sum.inl i)]
  rfl

variable {D : D7}

section Core

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

end Core

end GlobalTheory.Core.Rk.SW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocFlat.CFac
open scoped Topology

noncomputable section
namespace GlobalTheory.LocFlat.LastColumn

def colJoin (n n' k : Type) [TopologicalSpace k] : Matrix n n' k × (n → k) ≃ₜ Matrix n (n' ⊕ Unit) k where
  toFun p := fromCols p.1 (Matrix.of fun r _ => p.2 r)
  invFun M := (M.toCols₁, fun r => M r (Sum.inr ()))
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · funext r; simp
  right_inv M := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  continuous_toFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using (by fun_prop : Continuous fun a : Matrix n n' k × (n → k) => a.2 r)
  continuous_invFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_pi fun r => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · exact continuous_id.matrix_elem r (Sum.inr ())

def colSplit (n n' k : Type) [TopologicalSpace k] :
    Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, Matrix.of fun r _ => x r (Sum.inr ()))
  invFun p := fromCols p.1 p.2
  left_inv x := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · ext r u; cases u; simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_matrix fun r u => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · simpa using continuous_id.matrix_elem r (Sum.inr ())
  continuous_invFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using continuous_snd.matrix_elem r u

def rowSplit (n n' Z k : Type) [TopologicalSpace k] :
    Matrix n n' k × Matrix (Z ⊕ Unit) n k ≃ₜ (Matrix n n' k × (n → k)) × Matrix Z n k where
  toFun q := ((q.1, q.2 (Sum.inr ())), q.2.toRows₁)
  invFun p := (p.1.1, fromRows p.2 (Matrix.of fun _ => p.1.2))
  left_inv q := by
    obtain ⟨x, M⟩ := q
    refine Prod.ext rfl ?_
    ext (i | u) j
    · simp [toRows₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨⟨x, y⟩, A⟩ := p
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · funext j; simp
    · ext i j; simp [toRows₁]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk continuous_fst (continuous_pi fun j => ?_))
      (continuous_matrix fun i j => ?_)
    · exact continuous_snd.matrix_elem (Sum.inr ()) j
    · simpa [toRows₁] using continuous_snd.matrix_elem (Sum.inl i) j
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_fst) (continuous_matrix fun i j => ?_)
    cases i with
    | inl i => simpa using continuous_snd.matrix_elem i j
    | inr u => simpa using (by fun_prop : Continuous fun a : (Matrix n n' k × (n → k)) × Matrix Z n k => a.1.2 j)

theorem isLocallyConstant_integral {Q Y : Type} [TopologicalSpace Q] [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) {H : Q × Y → ℂ} (hH : IsLocallyConstant H) {K : Set Y} (hK : IsCompact K)
    (hz : ∀ q, ∀ y ∉ K, H (q, y) = 0) : IsLocallyConstant fun q => ∫ y, H (q, y) ∂μ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun q₀ => ?_
  have h1 : ∀ᶠ q in 𝓝 q₀, ∀ y ∈ K, H (q, y) = H (q₀, y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hK fun y _ => ?_
    have h2 : IsLocallyConstant fun p : Q × Y => (H p, H (q₀, p.2)) :=
      hH.prodMk (hH.comp_continuous (by fun_prop))
    filter_upwards [h2.eventually_eq (q₀, y)] with p hp
    simp only [Prod.mk.injEq] at hp
    exact hp.1.trans hp.2.symm
  filter_upwards [h1] with q hq
  congr 1
  funext y
  by_cases hy : y ∈ K
  · exact hq y hy
  · rw [hz q y hy, hz q₀ y hy]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem hatCol_mem_SB (ψ : AddChar k Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] {n n' : Type} [Fintype n] [DecidableEq n]
    {Ψ : Matrix n (n' ⊕ Unit) k → ℂ} (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) :
    (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) ∈
      SB (Matrix n n' k × (n → k)) := by
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  set f : Matrix n n' k × (n → k) → ℂ := fun p => Ψ (colJoin n n' k p) with hfdef
  have hf : f ∈ SB (Matrix n n' k × (n → k)) :=
    ⟨hΨ.1.comp_continuous (colJoin n n' k).continuous, hΨ.2.comp_homeomorph _⟩
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ FourierPi.box n s, ∀ x y, f (x, y + t) = f (x, y) := by
    have h1 := PartialFourier.eventually_add_invariant hf
    have h2 : Filter.Tendsto (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) := by fun_prop
      exact this.tendsto 0
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (h2.eventually h1)
    exact ⟨s, fun t ht x y => by simpa using hs ht (x, y)⟩
  have hfun : (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) =
      fun p => ∫ y, f (p.1, y) * (ψ (y ⬝ᵥ (-p.2)) : ℂ) ∂(Measure.pi fun _ => ν) := by
    funext p
    simp only [GlobalTheory.StepData.hat]
    congr 1
    funext y
    rw [dotProduct_neg, dotProduct_comm, neg_one_mul]
    rfl
  rw [hfun]
  refine ⟨?_, ?_⟩
  · refine isLocallyConstant_integral _
      (H := fun q : (Matrix n n' k × (n → k)) × (n → k) => f (q.1.1, q.2) * (ψ (q.2 ⬝ᵥ (-q.1.2)) : ℂ))
      ?_ (hf.2.image continuous_snd) ?_
    · refine (hf.1.comp_continuous (by fun_prop)).mul ?_
      exact (hc.isLocallyConstant.comp_continuous
        (continuous_snd.dotProduct (continuous_snd.comp continuous_fst).neg)).comp (fun z : Circle => (z : ℂ))
    · intro q y hy
      have : f (q.1, y) = 0 := image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, rfl⟩
      simp [this]
  · refine HasCompactSupport.intro
      ((hf.2.image continuous_fst).prod (FourierPi.isCompact_box (n := n) (c * s⁻¹)).neg) fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : ∀ y, f (p.1, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hp ⟨_, h, rfl⟩
      simp [this]
    · rw [Set.mem_neg] at hp
      exact FourierPi.fourier_eq_zero_pi _ hc (f := fun y => f (p.1, y)) (fun t ht y => hs t ht p.1 y) hp

theorem lastColumn_datum_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z], (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)), ∃ Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k), ∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)), ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ())) := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _
  haveI := hν
  refine ⟨fun Ψ₁ Ψ₂ => ?_, fun Ξ₁ c => ?_⟩
  · let F : SB (Matrix n n' k × (n → k)) := ⟨_, hatCol_mem_SB ψk hψ hne ν Ψ₁.2⟩
    exact ⟨comapH (rowSplit n n' Z k) (prodSB F Ψ₂), fun q => mul_comm _ _⟩
  · exact ⟨comapH (colSplit n n' k) (prodSB Ξ₁ c), fun x => rfl⟩

end GlobalTheory.LocFlat.LastColumn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasuresStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_measure_pushforward_eq_product_real_measures : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ENNReal, Measurable Z → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → MeasurableSet {h : GA D W | finE W h ∈ K} → ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν = ∫⁻ b, Z (realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  first | exact @GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi | exact GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi | (intros; apply GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi <;> assumption)
end

