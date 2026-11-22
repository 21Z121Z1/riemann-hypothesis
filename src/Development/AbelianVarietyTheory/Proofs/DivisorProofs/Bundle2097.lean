import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweredWeightInterpolationAtPoints
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

abbrev lamL (j : Fin D.R.m) (τ : D.what₂.Tau) : DomWeight (Vc D j).rank :=
  Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ

def lamT (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) : ℕ :=
  if h : a < (Vc D j).rank then (lamL j τ).natW ⟨a, h⟩ else 0

def cT (j : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((Vc D j).rank : ℝ) / 2 - 1 - ((lamL j τ).detShift : ℝ)

open Classical in

def wts (L : SizeData₂ D) (j : Fin D.R.m) : Wts D.what₂.Tau where
  lam := lamT j
  T2 := Finset.univ.filter fun τ => (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  j := fun _ => (j : ℕ) + 1
  q := fun _ => D.R.m - ((j : ℕ) + 1)
  xm := fun τ => ⌈cT j τ⌉
  xp := fun τ => ⌊cT j τ + L.Sc⌋
  c := cT j
  e := fun τ => wj D ((j : ℕ) + 1) τ
  fr := fun _ τ => τ
  cj := fun _ _ => false
  Sp := Formalism.MainNotions.JumpSetsAlt.excSet D

def ValsAt (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) : Prop :=
  (∀ (a : ℕ) (ha : a < D.R.k - 1),
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ)) ∧
    (∀ i : Fin D.R.m, (i : ℕ) ≤ j →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ)) ∧
    (∀ s : ℕ, s < D.R.t →
      ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) - (wts L j).c τ =
        -wj D ((j : ℕ) + 1) τ + ((D.R.t : ℝ) - 1) / 2 - s) ∧
    (∀ i : Fin D.R.m, (j : ℕ) < i →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i + D.R.t) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ))

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem lamT_of_lt (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (h : a < (Vc D j).rank) :
    (lamT j τ a : ℤ) = (lamL j τ).w ⟨a, h⟩ - (lamL j τ).detShift := by
  have hn : 0 < (Vc D j).rank := by omega
  have hle : (lamL j τ).detShift ≤ (lamL j τ).w ⟨a, h⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hn]
    exact (lamL j τ).anti (Fin.mk_le_mk.2 (by omega))
  unfold lamT DomWeight.natW
  rw [dif_pos h]
  omega

theorem anti (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ a b, a ≤ b → b < (parOf L j).Nr → (wts L j).lam τ b ≤ (wts L j).lam τ a := by
  intro τ a b hab hb
  have ha : a < (Vc D j).rank := lt_of_le_of_lt hab hb
  have h1 := lamT_of_lt j τ a ha
  have h2 := lamT_of_lt j τ b hb
  have h3 := (lamL j τ).anti (show (⟨a, ha⟩ : Fin _) ≤ ⟨b, hb⟩ from Fin.mk_le_mk.2 hab)
  show lamT j τ b ≤ lamT j τ a
  omega

theorem rank_eq (j : Fin D.R.m) : (Vc D j).rank = D.R.k - 1 + D.R.m + D.R.t := by
  have h := D.sp.V_rank ((j : ℕ) + 1) (by omega) (by omega)
  have hk := D.R.m_add_three_le_k
  simp only [Vc, h, Ranks.nV, Ranks.r]
  omega

theorem what₂ (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ, Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t + (wts L j).q τ = (parOf L j).Nr := by
  intro τ
  have := rank_eq j
  have hj := j.2
  simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]
  omega

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem U_last (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    (wts L j).U (parOf L j) τ ((Vc D j).rank - 1) = 0 := by
  have hn := rank_eq j
  have ht0 := D.R.t_odd.pos
  have hlt : (Vc D j).rank - 1 < (Vc D j).rank := by omega
  have h1 := lamT_of_lt j τ _ hlt
  have h2 : (lamL j τ).detShift = (lamL j τ).w ⟨(Vc D j).rank - 1, hlt⟩ := by
    unfold DomWeight.detShift; rw [dif_pos (by omega)]
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) ((Vc D j).rank - 1) = 0
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem liftWeightCombinatorialData_U_le_U_zero (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    (wts L j).U (parOf L j) τ a ≤ (wts L j).U (parOf L j) τ 0 := by
  have h := anti L j τ 0 a (Nat.zero_le _) ha
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) 0
  change lamT j τ a ≤ lamT j τ 0 at h
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem U_nonneg (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    0 ≤ (wts L j).U (parOf L j) τ a := by
  show 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem T2_card (L : SizeData₂ D) (j : Fin D.R.m) : (wts L j).T2.card ≤ D.host.T2.card := by
  classical
  calc (wts L j).T2.card ≤ D.host.thickPlaces.card := by
        refine Finset.card_le_card_of_injOn (fun τ => (D.eTau τ : D.R.GG)) ?_ ?_
        · intro τ hτ
          simp only [wts, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ
          exact hτ
        · intro a _ b _ h
          exact D.eTau.injective (Subtype.ext h)
    _ ≤ D.host.T2.card := by
        unfold Host.thickPlaces
        exact Finset.card_image_le

theorem c_le (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ) :
    (wts L j).c τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := by
  have hn := rank_eq j
  have hU := U_last L j τ
  have ht : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have ht0 := D.R.t_odd.pos
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  by_cases hj : (j : ℕ) + 1 < D.R.m
  · have h := hv.2.2.2 ⟨D.R.m - 1, by omega⟩ (by simp; omega)
    have hrow : D.R.k - 1 + (D.R.m - 1) + D.R.t = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hg := (D.hc τ).gap_be ⟨D.R.m - 1, by omega⟩
    have hw : wj D D.R.m τ = (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dif_pos (by omega)]
    have hg' : (((D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) + ((D.R.t : ℝ) + 3) / 2 ≤
        (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      have h2 : ((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) ≥ ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) := by
        exact_mod_cast hg
      push_cast at h2
      linarith
    push_cast at h
    rw [hw]; linarith
  · have hjm : (j : ℕ) + 1 = D.R.m := by omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hrow : D.R.k + (j : ℕ) + (D.R.t - 1) = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts, hjm] at h
    push_cast at h
    linarith

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactor
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinOp

theorem local_op_eq_smul : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    Acts (evFin F v) (om' (g, h)) φ φ₁ →
    ∃ (c : ℂ) (P : GL (Fin a') (Fv F v)) (Q : GL (Fin (a + a')) (Fv F v)), ∀ Y, ι φ₁ Y = c * ι φ (P.1 * Y * Q.1) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι g hg h hh φ hφ φ₁ hφ₁ hacts
  classical
  set co : Matrix (Fin a') (Fin (a + a')) (AE F E) → Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    fun u => -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
      (1 : GL (Fin (a + a')) (Fv F v)).1) with hco
  have hL : G.M'.IsLin B.ψ (piW (t.comp σ)) (piW t) co ι := hι
  have hP' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  obtain ⟨hex1, hex2, -⟩ := GlobalTheory.T.theta_action_exists hPr F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v

  have hex1' : ∀ ξ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, ∃ η, ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
      η ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, h)) ξ η := by
    intro ξ
    by_cases hξ : ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v)
    · obtain ⟨η, hη, -⟩ := hex1 g hg h hh ξ hξ
      exact ⟨η, fun _ => hη⟩
    · exact ⟨0, fun h' => absurd h' hξ⟩
  choose T hTspec using hex1'

  set ιi := Function.invFunOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    with hιi
  have hinv := hL.bij.invOn_invFunOn
  have hi1 : ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ιi Ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ ι (ιi Ξ) = Ξ :=
    fun Ξ hΞ => ⟨hL.bij.surjOn.mapsTo_invFunOn hΞ, hinv.2 hΞ⟩
  have hi2 : ∀ ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ιi (ι ξ) = ξ := fun ξ hξ => hinv.1 hξ

  set gt := (mat g).map (piW t) with hgt
  set gi := (mat g⁻¹).map (piW t) with hgi
  set ht' := (mat h).map (piW t) with hht
  set hi := (mat h⁻¹).map (piW t) with hhi
  have hg1 : gt * gi = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g * mat g⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg2 : gi * gt = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g⁻¹ * mat g = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh1 : ht' * hi = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h * mat h⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh2 : hi * ht' = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h⁻¹ * mat h = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPP : giᵀ * gtᵀ = 1 := by rw [← Matrix.transpose_mul, hg1, Matrix.transpose_one]
  have hPP' : gtᵀ * giᵀ = 1 := by rw [← Matrix.transpose_mul, hg2, Matrix.transpose_one]

  have at_conj : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u →
      At (evFin F v) (mat g * u * (mat h)ᵀ) := by
    intro u hu c hc
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  have hmap : ∀ (f : AE F E →+* Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      (mat g * u * (mat h)ᵀ).map f = (mat g).map f * u.map f * ((mat h).map f)ᵀ := by
    intro f u
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hco_act : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), co (mat g * u * (mat h)ᵀ) = giᵀ * co u * hi := by
    intro u
    have hca : gtᵀ * co (mat g * u * (mat h)ᵀ) * ht' = co u := GlobalTheory.T.local_moment_matrix_transform F E σ a' (a + a') G.V' G.W v t g h u
    calc co (mat g * u * (mat h)ᵀ) = (giᵀ * gtᵀ) * co (mat g * u * (mat h)ᵀ) * (ht' * hi) := by
          rw [hPP, hh1, Matrix.one_mul, Matrix.mul_one]
      _ = giᵀ * (gtᵀ * co (mat g * u * (mat h)ᵀ) * ht') * hi := by simp only [Matrix.mul_assoc]
      _ = giᵀ * co u * hi := by rw [hca]

  set A : (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ) → Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ :=
    fun Ξ Y => ι (T (ιi Ξ)) (giᵀ * Y * hi) with hA
  have hlin : ∀ (c0 : ℂ), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ∀ Ξ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c0 • Ξ + Ξ') = c0 • A Ξ + A Ξ' := by
    intro c0 Ξ hΞ Ξ' hΞ'
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨hξ', hιξ'⟩ := hi1 Ξ' hΞ'
    have hs : c0 • ιi Ξ + ιi Ξ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := add_mem (Submodule.smul_mem _ c0 hξ) hξ'
    have e1 : ιi (c0 • Ξ + Ξ') = c0 • ιi Ξ + ιi Ξ' := by
      have : ι (c0 • ιi Ξ + ιi Ξ') = c0 • Ξ + Ξ' := by rw [map_add, map_smul, hιξ, hιξ']
      rw [← this]; exact hi2 _ hs
    obtain ⟨-, hTa1⟩ := hTspec _ hξ
    obtain ⟨-, hTa2⟩ := hTspec _ hξ'
    obtain ⟨-, hTa3⟩ := hTspec _ hs
    have e2 := GlobalTheory.T.local_action_linear_in_vector F (Fin a' × Fin (a + a')) v (om' (g, h)) c0 (ιi Ξ) (ιi Ξ') _ _ _ hξ hξ' hTa1 hTa2 hTa3
    funext Y
    show ι (T (ιi (c0 • Ξ + Ξ'))) (giᵀ * Y * hi) = c0 * ι (T (ιi Ξ)) (giᵀ * Y * hi) + ι (T (ιi Ξ')) (giᵀ * Y * hi)
    rw [e1, e2, map_add, map_smul]
    rfl
  have hA0 : A 0 = 0 := by
    have h0 := hlin 1 0 (zero_mem _) 0 (zero_mem _)
    simp only [one_smul, add_zero] at h0
    have h2 : A 0 + A 0 = A 0 + 0 := by rw [add_zero]; exact h0.symm
    exact add_left_cancel h2
  have hadd : ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), ∀ f' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (f + f') = A f + A f' := fun f hf f' hf' => by simpa using hlin 1 f hf f' hf'
  have hsmul : ∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c • f) = c • A f :=
    fun c f hf => by simpa [hA0] using hlin c f hf 0 (zero_mem _)

  have hut_map : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), ∀ f : AE F E →+* Fv F v, u.map f = 0 →
      (mat g * u * (mat h)ᵀ).map f = 0 := by
    intro u f hu
    rw [hmap, hu, Matrix.mul_zero, Matrix.zero_mul]
  have hsurj := fun Y => GlobalTheory.T.local_matrix_moment_surjective F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Y
  have htr : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => Ξ (Y + Z)) = fun Y => A Ξ (Y + Z) := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hcu⟩ := hsurj Z
    have hcu' : co u = Z := hcu
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => Ξ (Y + Z) := by
      funext Y
      rw [hL.trans u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ Y, hιξ, hcu']
    have e2 : ιi (fun Y => Ξ (Y + Z)) = ξ₁ := by rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    show ι (T (ιi (fun Y => Ξ (Y + Z)))) (giᵀ * Y * hi) = ι (T (ιi Ξ)) (giᵀ * (Y + Z) * hi)
    rw [e2, ← e3, hL.trans _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄, hco_act, hcu',
      Matrix.mul_add, Matrix.add_mul]

  have hmul : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * A Ξ Y := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hchar⟩ := GlobalTheory.T.local_matrix_moment_surjective_conj F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Z
    have hchar' : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, co x i j * Z i j) := hchar
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y := by
      funext Y
      obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
      have hcx' : co x = Y := hcx
      rw [← hcx', hL.mult u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ x hx hxt, hιξ, hchar' x hx hxt]
    have e2 : ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) = ξ₁ := by
      rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
    have hcx' : co x = Y := hcx
    have e4 : co (mat g * x * (mat h)ᵀ) = giᵀ * Y * hi := by rw [hco_act, hcx']
    have hs : symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
        symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u := GlobalTheory.T.symplectic_form_unitary_invariant F E σ a' (a + a') G.V' G.W g h x u
    show ι (T (ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y))) (giᵀ * Y * hi) =
      GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * ι (T (ιi Ξ)) (giᵀ * Y * hi)
    rw [e2, ← e3, ← e4, hL.mult _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄ _ (at_conj x hx)
      (hut_map x _ hxt), hs, hchar' x hx hxt, hcx']
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.additive_homogeneous_operator_linear (Fv F v) (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) a' (a + a') A hadd hsmul htr hmul
  have hιφ : ι φ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hL.bij.mapsTo hφ
  have eT : φ₁ = T φ := (hex1 g hg h hh φ hφ).unique ⟨hφ₁, hacts⟩ (hTspec φ hφ)
  refine ⟨cc, ⟨gtᵀ, giᵀ, hPP', hPP⟩, ⟨ht', hi, hh1, hh2⟩, fun Y => ?_⟩
  have key := congrFun (hcc (ι φ) hιφ) (gtᵀ * Y * ht')
  change ι (T (ιi (ι φ))) (giᵀ * (gtᵀ * Y * ht') * hi) = cc * ι φ (gtᵀ * Y * ht') at key
  have ee : giᵀ * (gtᵀ * Y * ht') * hi = Y := by
    simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hh1, Matrix.mul_one]
  rw [hi2 φ hφ, ← eT, ee] at key
  exact key

end GlobalTheory.OppLinOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivLOneBoundFamily
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop

namespace GlobalTheory

theorem log_deriv_L_one_le_along_family :
    GlobalTheory.FunPr.Hypotheses₂ → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ =>
      |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) := by
  intro _
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact ⟨0, fun x hx _ i _ _ => (Fm.params x hx i).logDerivative_le_power⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_group_order_bound : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  first | exact @GlobalTheory.CovTop.two_log_card_levels_le | exact GlobalTheory.CovTop.two_log_card_levels_le | (intros; apply GlobalTheory.CovTop.two_log_card_levels_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatementStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_weight_statement : LowAt := by
  first | exact @GlobalTheory.BigOn.Exp.lowAt_holds | exact GlobalTheory.BigOn.Exp.lowAt_holds | (intros; apply GlobalTheory.BigOn.Exp.lowAt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweredWeightInterpolationAtPointsStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.loweredWeight_interpolation_at_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∀ j : Fin Fl.δ, ∃ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom ∧ (∀ j', F (Fl.xs j') = if j' = j then 1 else 0) ∧ ∀ α : Fin (nd X.toData) → ℕ, ∑ q, α q ≤ Xa.T → (fun x => F x * monoM X.toData Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)) ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s) := by
  first | exact @GlobalTheory.LowerInterp.lowered_interp | exact GlobalTheory.LowerInterp.lowered_interp | (intros; apply GlobalTheory.LowerInterp.lowered_interp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVectorStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestTypeEquality_of_evaluationVector : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ u : U, (∀ w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w₀ ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w₀)) → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  first | exact @GlobalTheory.EvalLowType.lowType_of_eval | exact GlobalTheory.EvalLowType.lowType_of_eval | (intros; apply GlobalTheory.EvalLowType.lowType_of_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEvaluationSelfLinearStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_evaluation_self_linear : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n d,
    (∀ (z : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (f Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  first | exact @GlobalTheory.ThK.EvChangeUniq.eq_smul_isEv | exact GlobalTheory.ThK.EvChangeUniq.eq_smul_isEv | (intros; apply GlobalTheory.ThK.EvChangeUniq.eq_smul_isEv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtCompStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twAdm' : TwAdm := by
  first | exact @GlobalTheory.BigOn.Exp.twAdm | exact GlobalTheory.BigOn.Exp.twAdm | (intros; apply GlobalTheory.BigOn.Exp.twAdm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRowStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationality_of_twist_row : TwAdm → RowAt → TieRat := by
  first | exact @GlobalTheory.BigOn.Exp.tieRat_of | exact GlobalTheory.BigOn.Exp.tieRat_of | (intros; apply GlobalTheory.BigOn.Exp.tieRat_of <;> assumption)
end

