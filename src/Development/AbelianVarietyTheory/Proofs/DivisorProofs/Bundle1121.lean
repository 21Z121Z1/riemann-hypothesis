import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRank
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRowAnti

variable {D : D7}

theorem lam_step (τ : D.what₂.Tau) (n : ℕ) (hn : n + 1 < D.R.r) :
    Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1) + 1 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n := by
  have h := Formalism.L2.NTheta.lamAt_lt (D.hc τ) n hn
  obtain ⟨a, ha⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (n + 1)
  obtain ⟨b, hb⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  rw [ha, hb] at h ⊢
  have : a < b := by exact_mod_cast h
  have : a + 1 ≤ b := this
  exact_mod_cast this

theorem pq_eq (i : Fin D.R.m) (ρ : D.what₂.Tau) : pW D i ρ + qW D i ρ = D.R.r := by
  have h := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2] at h
  exact h

theorem aPl_anti (i : Fin D.R.m) (p : ℕ) (τ : D.what₂.Tau) (hp : p ≤ D.R.r) : Antitone (aPl D i p τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aPl
  by_cases h1 : n + 1 < p
  · rw [if_pos h1, if_pos (by omega : n < p)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have := lam_step τ n (by omega)
    push_cast
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

theorem aMi_anti (i : Fin D.R.m) (p q : ℕ) (τ : D.what₂.Tau) (hpq : p + q = D.R.r) : Antitone (aMi D i p q τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aMi
  by_cases h1 : n + 1 < q
  · rw [if_pos h1, if_pos (by omega : n < q)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have e1 : p + (q - n) - 1 = (p + (q - (n + 1)) - 1) + 1 := by omega
    have := lam_step τ (p + (q - (n + 1)) - 1) (by omega)
    rw [e1]
    have e2 : ((q - n : ℕ) : ℚ) = ((q - (n + 1) : ℕ) : ℚ) + 1 := by
      rw [show q - n = (q - (n + 1)) + 1 by omega]; push_cast; ring
    rw [e2]
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

end GlobalTheory.LowRowAnti

open GlobalTheory.LowRowAnti in
theorem GlobalTheory.LowRow.lift_rows_antitone : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau),
    Antitone (aPlAt D i σ ρ) ∧ Antitone (aMiAt D i σ ρ) ∧ pW D i ρ + qW D i ρ = (Wc D i).rank ∧
      (Wc D i).rank ≤ (Vc D i).rank := by
  intro D i σ ρ
  have hpq := pq_eq (D := D) i ρ
  refine ⟨?_, ?_, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ, ?_⟩
  · exact aPl_anti i _ _ (by omega)
  · exact aMi_anti i _ _ _ hpq
  · rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact r_le_V i
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsEquivariantTwistedAndPlainModels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.GEqBr

set_option maxHeartbeats 2000000 in

theorem geq_br : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.phase → R.PGEquiv F → (∀ t g (v : (A3.A.MtildeCSD t).Forms), R.Th t (R.jX t (A3.A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) ∧ ∀ i t g (v : (A3.A.MtCSD i t).Forms), R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A3.A) g (R.thG i t (R.jV i t v)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hph hG
  refine ⟨fun t g v => hG.1 t g v, fun i t g v => ?_⟩
  have h : cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) =
      R.gW i (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t v)) := hG.2 i t g v
  rw [map_smul] at h
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hph i).1, norm_zero] at this
    exact one_ne_zero this
  exact smul_right_injective _ hne h

end GlobalTheory.GEqBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.VB

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.coe_lt_top n))
    | coe m =>
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem suppDim_lt_of_genRank_eq_zero {n : ℕ} (hd : topologicalKrullDim Z ≤ (n : WithBot ℕ∞))
    {F : Z.Modules} [QCoh.IsFiniteQC F] (h : genRank F = 0) : QCoh.suppDim F < (n : WithBot ℕ∞) := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z := by
    rw [← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact lt_of_add_one_le_natCast (this.trans hd)

variable {κ : Type} [Field κ] [Algebra κ Γ(Z, ⊤)]

theorem interNum_of_genRank_eq (hp : IsProjOver (strHom κ Z)) {ι : Type} [Fintype ι]
    (hd : topologicalKrullDim Z ≤ (Fintype.card ι : ℕ)) {P : ι → LB Z} (hP : ∀ i, (P i).IsLB)
    (r : ℕ) : ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    rw [interNum_eq_zero_of_isProjOver hf G hp (suppDim_lt_of_genRank_eq_zero hd h) hP]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := Fintype.card ι) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist le_rfl hP hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hP h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

end GlobalTheory.VB

theorem GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver : ∀ (κ : Type) [Field κ] (Z : Scheme.{0})
    [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι],
    topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G]
    (P : ι → LB Z), (∀ i, (P i).IsLB) →
    interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P :=
  fun _ _ _ _ _ hp _ _ hd G _ _ hP => GlobalTheory.VB.interNum_of_genRank_eq hp hd hP _ G rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
section
noncomputable section

namespace GlobalTheory.UnrEuler

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def conjO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

theorem conjO_le (σ : E →ₐ[F] E) : (𝓞 E)⁰ ≤ Submonoid.comap (conjO σ) (𝓞 E)⁰ := by
  intro x hx
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at *
  intro h
  apply hx
  have h' : σ (x : E) = 0 := by
    simpa [conjO, RingOfIntegers.mapRingHom_apply] using congrArg (fun y : 𝓞 E => (y : E)) h
  exact RingOfIntegers.coe_eq_zero_iff.1 ((map_eq_zero_iff σ σ.toRingHom.injective).1 h')

def conjI (σ : E →ₐ[F] E) (𝔠 : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.extended E (conjO_le σ) 𝔠

variable (E) in

def diffE : FractionalIdeal (𝓞 E)⁰ E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)

def idA (σ : E →ₐ[F] E) (𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 E)⁰ E :=
  𝔟 * (conjI σ 𝔠)⁻¹ * (diffE E)⁻¹

def nrm (𝔞 : FractionalIdeal (𝓞 E)⁰ E) : ℝ := ((FractionalIdeal.absNorm 𝔞 : ℚ) : ℝ)

def unrFac (ν : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (s : ℂ) (v : Pl F) : ℂ :=
  (∏ w ∈ aboveF (L := E) F v, ((val ν w ^ FractionalIdeal.count E w 𝔞 : ℂˣ) : ℂ) *
    npow w (-(s * (FractionalIdeal.count E w 𝔞 : ℂ)))) * Lv (charFam ν) v s

variable (F) in

def kaOne (a a' : ℕ) (𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E) : ℝ :=
  (nrm 𝔠 * |(discr F : ℝ)|) ^ (-(a : ℝ) / 2) * nrm 𝔟 ^ (-(((a + a' : ℕ) : ℝ) - 2) / 2)

variable (F) in

def kaZero (a' : ℕ) (𝔠 : FractionalIdeal (𝓞 E)⁰ E) : ℝ := (nrm 𝔠 * |(discr F : ℝ)|) ^ (-(a' : ℝ) / 2)

theorem nrm_pos {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔞 ≠ 0) : 0 < nrm 𝔞 := by
  unfold nrm
  have := FractionalIdeal.absNorm_nonneg 𝔞
  have h2 : FractionalIdeal.absNorm 𝔞 ≠ 0 := by
    rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact_mod_cast lt_of_le_of_ne this (Ne.symm h2)

theorem locChar_eq_val_zpow {ν : Chr F E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt ν w)
    {b : (w.adicCompletion E)ˣ} {k : ℤ} (hb : Valued.v (b : w.adicCompletion E) = WithZero.exp (-k)) :
    locChar ν w b = val ν w ^ k := by
  have hϖ := Formalism.L2.Host.unif_spec w
  unfold Formalism.L2.Host.IsUnifAt at hϖ
  set ϖ := Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)
  have hu : Formalism.L2.Host.IsUnitAt w (b * ϖ⁻¹ ^ k) := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_inv_eq_inv_val, map_inv₀, hb, hϖ,
      ← WithZero.exp_neg, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h1 := h _ hu
  rw [map_mul, map_zpow, map_inv] at h1
  have h2 : val ν w = locChar ν w ϖ := rfl
  rw [h2]
  rw [inv_zpow, mul_inv_eq_one] at h1
  exact h1

theorem conjI_ne_zero (σ : E →ₐ[F] E) {𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔠 ≠ 0) : conjI σ 𝔠 ≠ 0 := by
  refine FractionalIdeal.extended_ne_zero E (conjO_le σ) ?_ h (zero_notMem_nonZeroDivisors)
  intro x y hxy
  apply RingOfIntegers.ext
  have : σ (x : E) = σ (y : E) := by
    simpa [conjO, RingOfIntegers.mapRingHom_apply] using congrArg (fun z : 𝓞 E => (z : E)) hxy
  exact σ.toRingHom.injective this

theorem diffE_ne_zero : diffE E ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem nu_triv (B : Base F E) {a a' : ℕ} (X : Chars F E) (hX : X.IsGood B a a') (he : Even (a + a')) (x : (AF F)ˣ) :
    X.ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1 := by
  have hα := hX.resα x
  have hβ := hX.resβ x
  have hp : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    have h1 : ((-1 : ℂ)) ^ a * (-1) ^ a' = 1 := by rw [← pow_add, he.neg_one_pow]
    have h2 : ((-1 : ℂ)) ^ a * (-1) ^ a = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) (h1.trans h2.symm)
  rw [Chars.ν, MonoidHom.div_apply, div_eq_one]
  apply Circle.coe_injective
  rw [hα, hβ]
  split_ifs
  · rfl
  · exact hp

theorem idealVal_mul (ν : Chr F E) {I J : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealVal ν (I * J) = idealVal ν I * idealVal ν J := by
  unfold idealVal
  simp_rw [FractionalIdeal.count_mul E _ hI hJ, zpow_add]
  apply finprod_mul_distrib
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors J)).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])

theorem idealVal_inv (ν : Chr F E) (I : FractionalIdeal (𝓞 E)⁰ E) : idealVal ν I⁻¹ = (idealVal ν I)⁻¹ := by
  unfold idealVal
  simp_rw [FractionalIdeal.count_inv, zpow_neg]
  exact finprod_inv_distrib _

end GlobalTheory.UnrEuler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwist
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

noncomputable section

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem pow_apply_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (x : Ideles E) : ((ξ.1 x : ℂˣ) : ℂ) ^ N = 1 := by
  have h1 : ((ξ ^ N : HChar E).1 x) = (ξ.1 x) ^ N := by
    rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rw [← Units.val_pow_eq_pow_val, ← h1, h]
  rfl

theorem locK_pow_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ((ξ.locK w x : ℂˣ) : ℂ) ^ N = 1 :=
  pow_apply_eq_one h _

theorem isUnitary_of_orderDvd {ξ : HChar E} {N : ℕ} (hN : 0 < N) (h : ξ.OrderDvd N) : IsUnitary ξ := fun x =>
  Complex.norm_eq_one_of_pow_eq_one (pow_apply_eq_one h x) hN.ne'

theorem expAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.UnrAt w) (hξ : ExpAt ξ w a) :
    ExpAt (χ * ξ) w a := by
  intro k
  have hk : χ.LevelLe w k := hχ.levelLe k
  refine ⟨fun hx => (hξ k).1 ?_, fun hn => hk.mul ((hξ k).2 hn)⟩
  have := hk.inv.mul hx
  rwa [inv_mul_cancel_left] at this

theorem psiAt_natMul (w : HeightOneSpectrum (𝓞 E)) (t : w.adicCompletion E) (k : ℕ) :
    psiAt w ((k : w.adicCompletion E) * t) = psiAt w t ^ k := by
  induction k with
  | zero => simpa using psiAt_eq_one (w := w) (t := 0) (by simp)
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, psiAt_add, ih, pow_succ]

theorem gaussSumAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w) {a : ℕ} (ha : a ≠ 0) (c : Eˣ) :
    gaussSumAt (χ * ξ) w a c = gaussSumAt ξ w a c := by
  unfold gaussSumAt
  congr 1
  funext y
  have hy := out_notMem w ha y
  have hy1 : w.valuation E ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) = 1 :=
    (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have hz0 : ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) ≠ 0 := fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  rw [gaussTerm, gaussTerm, dif_neg hz0, dif_neg hz0]
  have h1 : χ.locK w (Units.mk0 _ hz0) = 1 := by
    refine hχ _ ?_
    show Valued.v (((atFin w (Units.mk0 _ hz0)) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_mk0]
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval, hy1]
  have e : (χ * ξ).locK w (Units.mk0 _ hz0) = χ.locK w (Units.mk0 _ hz0) * ξ.locK w (Units.mk0 _ hz0) := rfl
  rw [e, h1, one_mul]

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem exists_gaussSumAt_dvd {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {q N : ℕ} (hq : q.Prime) (hqw : Ideal.absNorm w.asIdeal = q) (hN : 0 < N) (hξN : ξ.OrderDvd N) (hξ : ExpAt ξ w 1)
    (hξK : ∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) (hqK : ∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) :
    ∃ g : 𝓞 K, σ (g : K) = gaussSumAt ξ w 1 (unif w ^ (1 + diffExp w)) ∧ g ∣ (q : 𝓞 K) := by
  classical
  set c : Eˣ := unif w ^ (1 + diffExp w) with hc
  haveI : Fintype (𝓞 E ⧸ w.asIdeal ^ 1)ˣ := Fintype.ofFinite _
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hqv : w.valuation E ((q : 𝓞 E) : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have h := valuation_sub_le (w := w) (a := 1) (y := (q : 𝓞 E)) (y' := 0)
      (by rw [sub_zero, pow_one, ← hqw]; exact Ideal.absNorm_mem _)
    simpa using h
  have hterm : ∀ y : (𝓞 E ⧸ w.asIdeal ^ 1)ˣ, ∃ x : K,
      σ x = gaussTerm ξ w c ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1) : 𝓞 E) : E) ∧ x ^ (N * q) = 1 := by
    intro y
    have hy := out_notMem w one_ne_zero y
    set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1)
    have hy1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
    have hz0 : (z : E) ≠ 0 := fun h => by
      rw [h, map_zero] at hy1
      exact zero_ne_one hy1
    rw [gaussTerm, dif_neg hz0]
    obtain ⟨x1, hx1⟩ := hξK (Units.mk0 _ hz0)⁻¹
    have hp : psiAt w (algebraMap E (w.adicCompletion E) ((z : E) / c)) ^ q = 1 := by
      rw [← psiAt_natMul]
      apply psiAt_eq_one
      have e : ((q : ℕ) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) ((z : E) / c) =
          algebraMap E (w.adicCompletion E) (((q : 𝓞 E) : E) * ((z : E) / c)) := by simp
      rw [e, hval, map_mul, map_div₀, hy1, hc, valuation_unif_pow, one_div, ← div_eq_mul_inv,
        div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
      convert hqv using 2
      push_cast
      ring
    obtain ⟨x2, hx2⟩ := hqK _ hp
    have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
    have hx2q : x2 ^ q = 1 := σ.injective (by rw [map_pow, hx2, hp, map_one])
    refine ⟨x1 * x2, by rw [map_mul, hx1, hx2, map_inv], ?_⟩
    rw [mul_pow, pow_mul, hx1N, one_pow, one_mul, mul_comm N q, pow_mul, hx2q, one_pow]
  choose X hX using hterm
  have hpos : 0 < N * q := Nat.mul_pos hN hq.pos
  have hXi : ∀ y, IsIntegral ℤ (X y) := fun y => IsIntegral.of_pow hpos (by rw [(hX y).2]; exact isIntegral_one)
  have hXi' : ∀ y, IsIntegral ℤ (X y)⁻¹ := fun y =>
    IsIntegral.of_pow hpos (by rw [inv_pow, (hX y).2, inv_one]; exact isIntegral_one)
  have hnorm : ∀ y, ‖σ (X y)‖ = 1 := fun y =>
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, (hX y).2, map_one]) hpos.ne'
  have hgi : IsIntegral ℤ (∑ y, X y) := IsIntegral.sum _ fun y _ => hXi y
  have hgi' : IsIntegral ℤ (∑ y, (X y)⁻¹) := IsIntegral.sum _ fun y _ => hXi' y
  have hσg : σ (∑ y, X y) = gaussSumAt ξ w 1 c := by
    rw [map_sum, gaussSumAt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun y _ => (hX y).1
  have hσg' : σ (∑ y, (X y)⁻¹) = starRingEnd ℂ (gaussSumAt ξ w 1 c) := by
    rw [← hσg, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [map_inv₀, Complex.inv_eq_conj (hnorm y)]
  have hu : IsUnitary ξ := isUnitary_of_orderDvd hN hξN
  have hG := GlobalTheory.GaussMod.gaussSumAt_normSq ξ w 1 c one_ne_zero hξ hu (valuation_unif_pow w _)
  have hprod : (∑ y, X y) * (∑ y, (X y)⁻¹) = (q : K) := σ.injective (by
    rw [map_mul, hσg, hσg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hG, hqw, map_natCast]
    push_cast
    ring)
  refine ⟨⟨_, hgi⟩, hσg, ⟨⟨_, hgi'⟩, RingOfIntegers.ext ?_⟩⟩
  have e : ((q : 𝓞 K) : K) = (q : K) := by simp
  rw [e, ← hprod]
  rfl

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

theorem locEps_tame_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  intro E _ _ K _ _ _ σ χ ξ w q m N s hq hcard hqm hN hξN hχ hξ hξK hqK hs
  have hqw : Ideal.absNorm w.asIdeal = q := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hcard
  refine ⟨expAt_unr_mul hχ hξ, ?_⟩
  obtain ⟨gG, hgG, hdvd⟩ := exists_gaussSumAt_dvd σ hq hqw hN hξN hξ hξK hqK
  obtain ⟨x1, hx1⟩ := hξK (unif w ^ (1 + diffExp w))
  have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
  have hx1i : IsIntegral ℤ x1 := IsIntegral.of_pow hN (by rw [hx1N]; exact isIntegral_one)
  set a1 : 𝓞 K := ⟨x1, hx1i⟩ with ha1d
  have ha1 : IsUnit a1 := by
    have e : ((a1 : 𝓞 K) : K) = x1 := rfl
    exact IsUnit.of_pow_eq_one (RingOfIntegers.ext (by push_cast; exact (congrArg (· ^ N) e).trans hx1N)) hN.ne'
  have hqm' : (q : 𝓞 K) ∣ (m : 𝓞 K) := Nat.cast_dvd_cast hqm
  refine ⟨x1 * (q : K) ^ (-s).toNat * (gG : K), ?_, ?_⟩
  · have h1 : GlobalTheory.Square.IsAwayUnit m x1 := GlobalTheory.Square.IsAwayUnit.of_dvd (a := a1) (k := 0) (by simpa using ha1.dvd)
    have h2 : GlobalTheory.Square.IsAwayUnit m ((q : K) ^ (-s).toNat) := by
      have := GlobalTheory.Square.IsAwayUnit.of_dvd (K := K) (m := m) (a := (q : 𝓞 K) ^ (-s).toNat) (pow_dvd_pow_of_dvd hqm' _)
      simpa using this
    have h3 : GlobalTheory.Square.IsAwayUnit m (gG : K) := GlobalTheory.Square.IsAwayUnit.of_dvd (k := 1) (by rw [pow_one]; exact hdvd.trans hqm')
    exact (h1.mul h2).mul h3
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hj : (((-s).toNat : ℕ) : ℂ) = -(s : ℂ) := by
      have : (((-s).toNat : ℕ) : ℤ) = -s := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have e1 : ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((1 + diffExp w : ℕ) : ℂ)) =
        ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((0 + diffExp w : ℕ) : ℂ)) * (q : ℂ) ^ ((-s).toNat) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, hj]
      congr 1
      push_cast
      ring
    have e2 : (χ * ξ).locK w (unif w ^ (1 + diffExp w)) =
        χ.val w * χ.locK w (unif w ^ (0 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) := by
      show χ.locK w (unif w ^ (1 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) = _
      rw [pow_add, pow_one, map_mul, zero_add]
      rfl
    rw [locEps, locEps, if_neg one_ne_zero, if_pos rfl, gaussSumAt_unr_mul hχ one_ne_zero, hqw, e1, e2, map_mul, map_mul,
      hx1, hgG, map_pow σ, map_natCast σ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end GlobalTheory.TameTwistEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapComplexRightDerivativeEqStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicityMap_complexRightDerivative_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  first | exact @GlobalTheory.MultDer.rderC_eq | exact GlobalTheory.MultDer.rderC_eq | (intros; apply GlobalTheory.MultDer.rderC_eq <;> assumption)
end

