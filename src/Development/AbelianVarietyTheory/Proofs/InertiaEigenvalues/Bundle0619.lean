import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0015
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardHodgeTateJumpsCrystallineEqDim
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.Per.LetterJumps

theorem card_jumps_letter : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  intro l _ P AI hT H K LL hA V _ _ _ _ _ ρ U hC hU i
  classical
  obtain ⟨T⟩ := hT
  haveI := LL.2
  haveI := (P.PD K).finK
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  let eK : ↥K.1 ≃ₐ[ℚ_[l]] ↥(K0 K) := IntermediateField.equivOfEq e.symm
  let τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 := ((H.W K 1 LL hA.2.2).emb i).comp eK.toAlgHom
  have hτ : tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ := by
    refine AlgHom.ext fun x => ?_
    show (H.W K 1 LL hA.2.2).emb i (eK (algebraMap ↥(K0 K) ↥K.1 x)) = (H.W K 1 LL hA.2.2).emb i x
    congr 1
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
    rw [← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)),
      ← Nat.card_congr (Equiv.ofBijective _ (H.W K 1 LL hA.2.2).emb_bij), Nat.card_zmod]
    exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hdim := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI T K LL V ρ).2 hc
    (GlobalTheory.TopSteps.CrysRules.isDR T K LL ρ hC) τ
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ).1
  haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) ρ τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) ρ τ
  obtain ⟨b0, hb0⟩ := (U i).toFinset.bddBelow
  obtain ⟨b1, hb1⟩ := (U i).toFinset.bddAbove
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℤ, m ≤ lo ∧ m ≤ b0 ∧ m ≤ hi :=
    ⟨min (min lo b0) hi, by omega, by omega, by omega⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, hi ≤ k ∧ b1 < k := ⟨max hi (b1 + 1), by omega, by omega⟩
  have hmk : m ≤ k := by omega
  have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) ρ τ m k hmk
  rw [hlo m hm1, hhi k hk1, finrank_bot, Nat.cast_zero, sub_zero, hdim] at hsum
  have hsub : (U i).toFinset ⊆ Finset.Ico m k := fun a ha => by
    have h0 := hb0 (Finset.mem_coe.2 ha)
    have h1 := hb1 (Finset.mem_coe.2 ha)
    rw [Finset.mem_Ico]
    omega
  have hcnt : ∑ a ∈ Finset.Ico m k, ((U i).count a : ℤ) = (Multiset.card (U i) : ℤ) := by
    rw [← Multiset.toFinset_sum_count_eq, Nat.cast_sum]
    exact (Finset.sum_subset hsub fun a _ ha => by
      rw [Multiset.mem_toFinset] at ha
      rw [Multiset.count_eq_zero.2 ha, Nat.cast_zero]).symm
  have := (Finset.sum_congr rfl fun a _ => hU i τ hτ a).symm.trans hsum
  rw [hcnt] at this
  exact_mod_cast this

end GlobalTheory.Per.LetterJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperators
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PresHecke

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Raw

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {I : Type} {inR : I → Prop} {isT isLoc : I → G → Prop}

theorem keepsDcRaw (P : ClassPres ι S σ ρ J χ) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (i : I) (hi : inR i) : Keeps P (dcL (W := W) (hA i)) := by
  obtain ⟨Lc, hL1, hL2, hL3⟩ := hloc i hi
  intro F hF hv
  refine ⟨dcOp_mem (hok i hi).2.2 Lc (fun a ha => hL1 _ ((hok i hi).2.1 a ha)) hL2 hL3 hF, fun h => ?_⟩
  exact InRg.sum _ _ fun a _ => hv _

open Classical in

def opRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) (i : I) : Module.End K S.Forms :=
  if hi : inR i then trE P hχ hρ (keepsDcRaw P hx hA hok hloc i hi) else if one i then 1 else 0

def heckeRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) : HeckeTie ι P (opRaw P hχ hρ hx hA hok hloc one) inR isT isLoc where
  hx := hx
  hA := hA
  hx_ok i hi := (hok i hi).1
  hA_loc i hi := (hok i hi).2.1
  chi_loc i hi k hk := by
    obtain ⟨Lc, hL1, _, hL3⟩ := hloc i hi
    exact hL3 k (hL1 _ hk)
  hDC i hi := (hok i hi).2.2
  op_eq i hi f := by
    unfold opRaw
    rw [dif_pos hi, ext_trE]
    rfl

end Raw

end GlobalTheory.PresHecke

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.CharChange GlobalTheory.PresHecke

theorem sideReal_ofPres : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  intro G Γ _ _ ι I c l isT isLoc K _ _ _ σ S G0 _ inR P hσ hρ red hsurj hker hx hA hok hloc one
  have hχ : ∀ k : l.J, ∃ b : K, σ b = (l.χ k : ℂ) := fun k => by rw [← l.ch_J]; exact hσ _
  exact ⟨actNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ,
    opRaw P hχ hρ hx hA hok hloc one,
    ⟨P, actTieNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ, heckeRaw P hχ hρ hx hA hok hloc one⟩,
    rfl, rfl, fun i hi => ⟨fun ho => by simp [opRaw, hi, ho], fun ho => by simp [opRaw, hi, ho]⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SubLevel

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Gen

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

def dcRel (J' : Subgroup G) : Setoid G where
  r h h' := ∃ (γ : Γ) (k : J'), h' = ι γ * h * (k : G)
  iseqv := {
    refl := fun h => ⟨1, 1, by simp⟩
    symm := fun {h h'} ⟨γ, k, e⟩ => ⟨γ⁻¹, k⁻¹, by rw [e, map_inv, Subgroup.coe_inv]; group⟩
    trans := fun {h h' h''} ⟨γ, k, e⟩ ⟨γ₂, k₂, e₂⟩ =>
      ⟨γ₂ * γ, k * k₂, by rw [e₂, e, map_mul, Subgroup.coe_mul]; group⟩ }

theorem stab_mono_mem {J J' : Subgroup G} (hJ : J' ≤ J) {y k : G} (hk : k ∈ J) {g : Γ}
    (hg : g ∈ stab ι J' (y * k)) : g ∈ stab ι J y := by
  rw [mem_stab ι] at hg ⊢
  have h1 : (y * k)⁻¹ * ι g * (y * k) ∈ J := hJ hg
  have e : y⁻¹ * ι g * y = k * ((y * k)⁻¹ * ι g * (y * k)) * k⁻¹ := by group
  rw [e]
  exact J.mul_mem (J.mul_mem hk h1) (J.inv_mem hk)

end Gen

section Main

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ) (J' : Subgroup G)

def yN (c : Quotient (dcRel ι J')) : G := P.y (P.decC c.out) * (P.decK c.out : G)

theorem yN_rel (c : Quotient (dcRel ι J')) : (dcRel ι J').r (yN P J' c) c.out := by
  show ∃ (γ : Γ) (k : J'), c.out = ι γ * yN P J' c * (k : G)
  refine ⟨P.decG c.out, 1, ?_⟩
  show c.out = ι (P.decG c.out) * (P.y (P.decC c.out) * (P.decK c.out : G)) * ((1 : J') : G)
  rw [Subgroup.coe_one, mul_one, ← mul_assoc]
  exact P.dec_spec c.out

theorem mk_yN (c : Quotient (dcRel ι J')) : Quotient.mk (dcRel ι J') (yN P J' c) = c :=
  (Quotient.sound (yN_rel P J' c)).trans (Quotient.out_eq c)

theorem reps_new : IsReps ι J' (yN P J') := by
  intro h
  refine ⟨Quotient.mk (dcRel ι J') h, ?_, ?_⟩
  · exact Quotient.exact (mk_yN P J' (Quotient.mk (dcRel ι J') h))
  · rintro i ⟨γ, k, e⟩
    have hr : (dcRel ι J').r (yN P J' i) h := ⟨γ, k, e⟩
    exact (mk_yN P J' i).symm.trans (Quotient.sound hr)

theorem stabN_finite (hJ : J' ≤ J) (c : Quotient (dcRel ι J')) : Finite (stab ι J' (yN P J' c)) := by
  haveI : Finite (stab ι J (P.y (P.decC c.out))) := Finite.of_equiv _ (P.stabI (P.decC c.out)).toEquiv
  refine Finite.of_injective
    (fun g : stab ι J' (yN P J' c) =>
      (⟨(g : Γ), stab_mono_mem ι hJ (P.decK c.out).2 g.2⟩ : stab ι J (P.y (P.decC c.out)))) ?_
  intro a b hab
  have hv := congrArg Subtype.val hab
  exact Subtype.ext hv

include P in
theorem cl_finite (hfi : (J'.subgroupOf J).FiniteIndex) : Finite (Quotient (dcRel ι J')) := by
  haveI := hfi
  refine Finite.of_surjective
    (fun p : S.Cl × (J ⧸ J'.subgroupOf J) => Quotient.mk (dcRel ι J') (P.y p.1 * ((p.2.out : J) : G))) ?_
  intro c
  obtain ⟨d, γ, k, e⟩ : ∃ (d : S.Cl) (γ : Γ) (k : J), c.out = ι γ * P.y d * (k : G) :=
    ⟨_, _, _, P.dec_spec c.out⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (s := J'.subgroupOf J) k
  have hjJ' : ((j : J) : G) ∈ J' := Subgroup.mem_subgroupOf.1 j.2
  refine ⟨(d, (QuotientGroup.mk k : J ⧸ J'.subgroupOf J)), ?_⟩
  show Quotient.mk (dcRel ι J') (P.y d * (((QuotientGroup.mk k : J ⧸ J'.subgroupOf J).out : J) : G)) = c
  rw [hj]
  have hr : (dcRel ι J').r (P.y d * ((k * (j : J) : J) : G)) c.out := by
    refine ⟨γ, ⟨((j : J) : G)⁻¹, J'.inv_mem hjJ'⟩, ?_⟩
    show c.out = ι γ * (P.y d * ((k : G) * ((j : J) : G))) * ((j : J) : G)⁻¹
    rw [e]
    group
  exact (Quotient.sound hr).trans (Quotient.out_eq c)

variable (χ' : J' →* ℂˣ) (hχ' : ∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))

def rhoG (y : G) (g : stab ι J' y) (x : S.V) : W :=
  (χ' (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef x)

include hχ' hρ in
theorem rhoG_rg (y : G) (g : stab ι J' y) (x : S.V) : InRg P (rhoG P J' χ' y g x) := by
  obtain ⟨x', hx'⟩ := hρ (g : Γ) x
  obtain ⟨a, ha⟩ := hχ' (stabK ι g)
  refine ⟨a • x', ?_⟩
  rw [map_smulₛₗ, hx', ha]
  rfl

def rhoGE (y : G) (g : stab ι J' y) : Module.End K S.V where
  toFun x := cinv P (rhoG P J' χ' y g x)
  map_add' x x' := by
    apply coef_injective P
    rw [map_add, coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _),
      coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_add, smul_add]
  map_smul' b x := by
    apply coef_injective P
    rw [map_smulₛₗ, coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_smulₛₗ, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem coef_rhoGE (y : G) (g : stab ι J' y) (x : S.V) :
    P.coef (rhoGE P J' χ' hχ' hρ y g x) = rhoG P J' χ' y g x :=
  coef_cinv P (rhoG_rg P J' χ' hχ' hρ y g x)

def rhoGN (y : G) : stab ι J' y →* Module.End K S.V where
  toFun := rhoGE P J' χ' hχ' hρ y
  map_one' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [coef_rhoGE]
    simp [rhoG, stabK_one']
  map_mul' g g' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [Module.End.mul_apply, coef_rhoGE, coef_rhoGE]
    simp only [rhoG, coef_rhoGE, map_mul, stabK_mul', Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_smul,
      smul_smul, mul_comm]

end Main

end GlobalTheory.SubLevel

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.SubLevel

theorem classPres_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  intro G Γ _ _ ι W _ _ K _ _ _ σ S ρ J χ P J' hJ hfi χ' hχ' hρ
  haveI : Finite (Quotient (SubLevel.dcRel ι J')) := SubLevel.cl_finite P J' hfi
  letI fC : Fintype (Quotient (SubLevel.dcRel ι J')) := Fintype.ofFinite _
  haveI hfS : ∀ c, Finite (stab ι J' (SubLevel.yN P J' c)) := fun c => SubLevel.stabN_finite P J' hJ c
  letI fG : ∀ c, Fintype (stab ι J' (SubLevel.yN P J' c)) := fun c => Fintype.ofFinite _
  exact ⟨Quotient (SubLevel.dcRel ι J'), fC, fun c => P.decC c.out, fun c => P.decK c.out,
    fun c => stab ι J' (SubLevel.yN P J' c), fun c => inferInstance, fG,
    fun c => SubLevel.rhoGN P J' χ' hχ' hρ (SubLevel.yN P J' c),
    { y := SubLevel.yN P J'
      reps := SubLevel.reps_new P J'
      stabI := fun c => MulEquiv.refl _
      coef := P.coef
      coef_li := P.coef_li
      coef_span := P.coef_span
      coef_pair := P.coef_pair
      coef_act := fun c g x => SubLevel.coef_rhoGE P J' χ' hχ' hρ (SubLevel.yN P J' c) g x },
    fun c => rfl, rfl⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleClassAdmissible
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem GlobalTheory.admissible_eventually_iff_mem_cls : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0) →
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) →
    ∀ z : ↥(Z1 (twCoef W S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea W S.Γ.χ₁ ha z)) ↔
        Submodule.Quotient.mk z ∈ S.cls W X) := by
  intro l _ P S M _ _ W X _ _ _ hX hlev z
  constructor
  · rintro ⟨a₀, h⟩
    obtain ⟨a₁, h1⟩ := hX
    have hle1 : a₁ ≤ max a₀ (max a₁ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
    have ha : ∀ x : X, S.Γ.lam ^ (max a₀ (max a₁ 1)) • x = 0 := by
      intro x
      rw [← Nat.sub_add_cancel hle1, pow_add, mul_smul, h1, smul_zero]
    have hA := h (max a₀ (max a₁ 1)) (le_max_left _ _) ha
    have hone : 1 ≤ max a₀ (max a₁ 1) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hlev _ ha hone]
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mpr hA
  · intro h
    refine ⟨1, fun a ha1 ha => ?_⟩
    rw [hlev a ha ha1] at h
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mp h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlaces
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Proof.ConjugatePlaces

open GlobalTheory.IndefiniteRowSideFullHecke

section Host

variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem exists_conj_int (x : 𝓞 H.E) : ∃ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) :=
  ⟨⟨H.conj (x : H.E), (x.isIntegral_coe).map (H.conj.toAlgHom.restrictScalars ℤ)⟩, rfl⟩

variable {H}

theorem isConjPl_symm {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') : IsConjPl H w' w :=
  fun x y hy => (h y x (by rw [hy, conj_conj])).symm

theorem isConjPl_unique {w w₁ w₂ : HeightOneSpectrum (𝓞 H.E)} (h₁ : IsConjPl H w w₁)
    (h₂ : IsConjPl H w w₂) : w₁ = w₂ := by
  ext y
  obtain ⟨x, hx⟩ := exists_conj_int H y
  have hy : (y : H.E) = H.conj (x : H.E) := by rw [hx, conj_conj]
  exact (h₁ x y hy).symm.trans (h₂ x y hy)

variable (H)

end Host

section Loc

variable (D : D7) (i : D.nd.Loc)

section Pl

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Pl

def PairBody (ep : Bool) : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    SplitPlacesEmbeddingType.UnramPlace D i w hw ∧
    ∃ (wc : HeightOneSpectrum (𝓞 D.host.E)) (hwc : wc ∈ placesOver D.host.E (D.nd.l i)),
      IsConjPl D.host w wc ∧ wc ≠ w ∧
      ((SplitPlacesEmbeddingType.PlaceType D i w hw ep ∧ SplitPlacesEmbeddingType.PlaceType D i wc hwc (!ep)) ∨
        (SplitPlacesEmbeddingType.PlaceType D i w hw (!ep) ∧ SplitPlacesEmbeddingType.PlaceType D i wc hwc ep))) ∧
  ∃ col : Finset (HeightOneSpectrum (𝓞 D.host.E)), SplitPlacesEmbeddingType.IsTypeCol D i ep col ∧
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ wc, IsConjPl D.host w wc → (w ∈ col ↔ wc ∉ col)

end Loc

def OnLoc_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) →
    SplitPlaceTypes.PlacesSplit D.host (D.nd.l i) ∧ SplitPlaceTypes.TypesPair (N := D.nd) D.nbr i

def OffLoc_at (D : D7) : Prop :=
  ∀ l : ℕ, (∀ i : D.nd.Loc, D.nd.l i ≠ l) → SplitPlaceTypes.SplitRowPrime D.host l → SplitPlaceTypes.PlacesSplit D.host l

end GlobalTheory.Proof.ConjugatePlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBoundStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_extension_class_bound : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBat S E := by
  first | exact @GlobalTheory.Cyc.ClassBound.class_bound | exact GlobalTheory.Cyc.ClassBound.class_bound | (intros; apply GlobalTheory.Cyc.ClassBound.class_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionOfJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_extension_of_jumps : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (T : QLat LL) (U : Finset ℤ), (0 : ℤ) ∈ U → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)) → ∀ z : ↥(latticeCocycles T.L), IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ → ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z).ρ τ (U : Set ℤ) := by
  first | exact @GlobalTheory.ExtJumps.jumps_extLat | exact GlobalTheory.ExtJumps.jumps_extLat | (intros; apply GlobalTheory.ExtJumps.jumps_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfExtensionLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_of_extension_lattice : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL), IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ := by
  first | exact @GlobalTheory.ExtLatCrys.isCrys_resF_extLat | exact GlobalTheory.ExtLatCrys.isCrys_resF_extLat | (intros; apply GlobalTheory.ExtLatCrys.isCrys_resF_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorusStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  first | exact @GlobalTheory.JR.LinDesc.fubini_cutoff | exact GlobalTheory.JR.LinDesc.fubini_cutoff | (intros; apply GlobalTheory.JR.LinDesc.fubini_cutoff <;> assumption)
end

