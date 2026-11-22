import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof
import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SplitROfSteps
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0023
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeEveryTheory
section
namespace Formalism.MainNotions.UnusedSlot80

open Formalism.BasicNotions

theorem base_change_statement (D : D7) : H1fBaseChangeTheorem D := BCF.base_change_statement_of_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general D

theorem base_change_every_theory (Th : LocTheory) : Formalism.MainNotions.WachCoordinates.admBC Th := BCF.base_change_of_coefficient_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general Th

end Formalism.MainNotions.UnusedSlot80
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def InvLiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → invLiftR D HW

def ClassMapStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → classMapR D HW

def FrameStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → frameR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ColumnH0Lengths
section
noncomputable section

namespace Formalism.MainNotions.ColumnH0Lengths

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions NumberField IsDedekindDomain

variable {D : D7}

def ColumnLengthInvariantsBound (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop := InvariantsBoundConditions L X c

def CondCB (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    (X.cB i : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L

def H0CyclotomicLengthBound (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    (h0 D.nd i (X.dc i).col : ℝ) ≤ c * D.R.t

def H0ConstantBound (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ u ∈ (X.dc i).col, (X.c0 i u : ℝ) ≤ c * D.R.r * Formalism.MainNotions.TwistedPlaces.large₂ L

def H0BoundAtColumnPlace (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (X : HubData D) : Prop :=
  LocalSituation.Conclusion2 D HW F → ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D →
    Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ u ∈ (X.dc i).col, ∀ π ∈ D.nd.Zgood i,
      (Br.h0W i u (X.ρ i) π : ℝ) ≤ D.R.r * (X.c0 i u : ℝ)

def ColumnLengthHypotheses (L : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (X : HubData D) (c : ℝ) : Prop :=
  CondCB L X c ∧ H0CyclotomicLengthBound L X c ∧ H0ConstantBound L X c ∧ LocalSituation.Conclusion2 D HW F ∧ H0BoundAtColumnPlace HW F X

def ColumnLengthTheorem (L : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (X : HubData D) (c : ℝ) : Prop := ColumnLengthHypotheses L HW F X c → ColumnLengthInvariantsBound L X c

end Formalism.MainNotions.ColumnH0Lengths
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def GenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → genR D

def LiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → liftR D

def NormStep : Prop := ∀ D : D7, normR D

def DvdStep : Prop := dvdR

def QuotStep : Prop := ∀ D : D7, adm8 D → adm11 D → quotR D

def DeltaInvariantUniformizer : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → p9R D HW

def ExtStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → extOfR D HW

def WStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → wKillR D HW

def KerLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → FontExAll D HW F → kerLamR D HW

def NinLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → ninLamR D HW

def GradNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gradNR D HW

def FrobPiNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → frobPiNR D HW

def GamPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gamPiR D HW

def OneGenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → oneGenR D HW

def UnivStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → univR D HW

theorem killR_of_stepProps (hd : DvdStep) (hq : QuotStep) (hn : NormStep) (h9 : DeltaInvariantUniformizer)
    (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep) (hg : GradNStep)
    (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep) (hu : UnivStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), FontExAll D HW F → Adm1 D HW F Cm CA CB CK → killR D :=
  fun D HW F Cm CA CB CK hFont hA =>
    killR_of_steps D HW hd (hq D hA.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.1) (hn D)
      (h9 D HW F Cm hA.1)
      (splitR_of_steps D HW F hA.2.1 hA.2.2.2.2.1 (he D HW F Cm CA CB CK hA) (hw D HW F Cm CA CB CK hA)
        (hk D HW F Cm CA CB CK hA hFont) (hl D HW F Cm CA CB CK hA) (hg D HW F Cm CA CB CK hA)
        (hf D HW F Cm CA CB CK hA) (hγ D HW F Cm CA CB CK hA) (ho D HW F Cm CA CB CK hA))
      (hu D HW F Cm CA CB CK hA)

theorem local_theorem_of_lemma_properties (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep) (hu : UnivStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → IntegralityFromMetric D HW F Cm CA CB CK C :=
  fun D HW F Cm CA CB CK C hC hFont =>
    local_theorem_of_three_inputs D HW F Cm CA CB CK C hC (hG D HW F Cm CA CB CK) (hL D HW F Cm CA CB CK)
      (killR_of_stepProps hd hq hn h9 he hw hk hl hg hf hγ ho hu D HW F Cm CA CB CK hFont)

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfMemSum
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Comp

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_of_mem {τ : K →ₐ[Qp] LL} {y : V ⊗[Qp] BdR} (hy : y ∈ DdRE PD ρ τ) (c : K) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y = τ c • y := by
  have h := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hy).2 c
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
  exact h

theorem eq_zero_of_mem_sum (τ : K →ₐ[Qp] LL) :
    ∀ (s : Finset (K →ₐ[Qp] LL)), τ ∉ s → ∀ y ∈ DdRE PD ρ τ,
      y ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' → y = 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ y _ hy
    simpa using hy
  | insert a s ha ih =>
    intro hτ y hyτ hy
    have haτ : a ≠ τ := fun h => hτ (h ▸ Finset.mem_insert_self a s)
    have hτs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
    obtain ⟨c, hc⟩ : ∃ c : K, τ c ≠ a c := by
      by_contra h
      push_neg at h
      exact haτ (AlgHom.ext fun c => (h c).symm)

    let φ : Module.End LL (V ⊗[Qp] BdR) :=
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c - a c • LinearMap.id
    have hφ : ∀ τ', ∀ x ∈ DdRE PD ρ τ', φ x = (τ' c - a c) • x := by
      intro τ' x hx
      simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        mulVdR_of_mem PD ρ hx c, sub_smul]
    have hW : ∀ x ∈ ⨆ τ' ∈ s, DdRE PD ρ τ', φ x ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' := by
      intro x hx
      have hle : (⨆ τ' ∈ s, DdRE PD ρ τ') ≤ (⨆ τ' ∈ s, DdRE PD ρ τ').comap φ := by
        refine iSup₂_le fun τ' hτ' => fun z hz => ?_
        rw [Submodule.mem_comap, hφ τ' z hz]
        exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun τ' _ => DdRE PD ρ τ') τ' hτ') hz)
      exact hle hx
    rw [Finset.iSup_insert, Submodule.mem_sup] at hy
    obtain ⟨ya, hya, z, hz, hyz⟩ := hy
    have h1 : φ y ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' := by
      rw [← hyz, map_add, hφ a ya hya, sub_self, zero_smul, zero_add]
      exact hW z hz
    rw [hφ τ y hyτ] at h1
    have h2 := ih hτs _ (Submodule.smul_mem _ _ hyτ) h1
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc)

theorem mem_of_mem_filC (τ : K →ₐ[Qp] LL) (F : Submodule LL (V ⊗[Qp] BdR)) (hF : F ≤ DdRE PD ρ τ)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdRE PD ρ τ)
    (h : x ∈ F ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') : x ∈ F := by
  classical
  obtain ⟨f, hf, z, hz, hfz⟩ := Submodule.mem_sup.mp h
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hz
  have hle : (⨆ τ' ∈ s, ⨆ (_ : τ' ≠ τ), DdRE PD ρ τ') ≤ ⨆ τ' ∈ s.filter (· ≠ τ), DdRE PD ρ τ' := by
    refine iSup₂_le fun τ' hτ' => iSup_le fun hne => ?_
    exact le_iSup₂ (f := fun τ' _ => DdRE PD ρ τ') τ' (Finset.mem_filter.mpr ⟨hτ', hne⟩)
  have hzτ : z ∈ DdRE PD ρ τ := by
    have e : z = x - f := by rw [← hfz]; abel
    rw [e]
    exact Submodule.sub_mem _ hx (hF hf)
  have hz0 := eq_zero_of_mem_sum PD ρ τ (s.filter (· ≠ τ)) (by simp) z hzτ (hle hs)
  rw [← hfz, hz0, add_zero]
  exact hf

theorem fildR_eq_bot (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] (b : ℤ)
    (hj : JumpsInV PD ρ τ (Set.Iic (-b))) : ∀ a : ℤ, -b < a → FildR PD ρ τ a = ⊥ := by
  intro a ha
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (PD := PD) (ρ := ρ) τ
  have hstep : ∀ c : ℤ, -b < c → FildR PD ρ τ c = FildR PD ρ τ (c + 1) := by
    intro c hc
    by_contra h
    have h2 := hj c (fun h' => h h'.symm)
    exact absurd (Set.mem_Iic.1 h2) (not_le.2 hc)
  have hk : ∀ k : ℕ, FildR PD ρ τ a = FildR PD ρ τ (a + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, hstep (a + k) (by omega)]
      congr 1
      push_cast
      ring
  rw [hk (hi - a).toNat]
  exact hhi _ (by omega)

end Comp

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExtDataExtTool
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem extData_win (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) (hηb : η ≤ b i) :
    Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i ⊆
      Set.Icc (-(Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η i : ℤ)) (Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η i : ℤ) := by
  intro x hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.MiW Formalism.MainNotions.RamifiedCoefficientChains.hiW
  split_ifs at hx ⊢ with h <;> simp only [Set.mem_union, Set.mem_Icc] at hx ⊢ <;> push_cast at hx ⊢ <;> omega

theorem extData_lin {FF M I : Type} [AddCommGroup FF] [Module O FF] [AddCommGroup M] [Module O M] [Fintype I]
    (P : M → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : O) x, P x → P (c • x))
    (bF : Module.Basis I O FF) (Φ : FF →ₗ[O] M) (h : ∀ j, P (Φ (bF j))) (f : FF) : P (Φ f) := by
  rw [← bF.sum_equivFun f, map_sum]
  exact Finset.sum_induction _ P hadd h0 fun j _ => by rw [map_smul]; exact hsmul _ _ (h j)

theorem extData_extTool [NeZero n] (W : LocWach PD LL O v n)
    (hH : Formalism.MainNotions.ElementDenominator.coreHerrExtΔ W) (hExt : Formalism.MainNotions.LiftingTheory.liftb_HExt W) (hOne : Formalism.MainNotions.LiftingTheory.liftb_HOne W)
    (hKer : Formalism.MainNotions.LiftingTheory.liftb_HKer W) (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O)
    (hEx : ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
      IsSESLat (Qp := Qp) (O := O) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
        ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (hdex : W.DelF.card = PD.p - 1 → ∃ d : O, d * (W.DelF.card : O) = 1)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hQ : Formalism.MainNotions.CrystallineLiftingInputs.QTool W) :
    ExtTool W := by
  intro d T₁ T₂ F b S η m hS FF _ _ _ _ g
  have hS' := hS
  obtain ⟨hA, h11, -, hOd, hζ, hSur, hJ1, -, hab, -⟩ := hS
  have hηb : ∀ i, η ≤ b i := fun i => by
    have h0 := Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) (by omega)
    have h1 := hab i
    have h2 : (η : ℝ) ≤ (b i : ℝ) := by linarith
    exact_mod_cast h2
  set Mi := Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η with hMi
  set hi := Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η with hhi
  set a := ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊ with ha
  have c1 : IsCrys PD T₁.ρ := hSur.1
  have c2 : IsCrys PD T₂.ρ := hSur.2.1
  have hOc : IsCrys PD W.one.ρ := hOne.1
  have hJL1 : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi := fun i τ hτ x hx => extData_win d b S η i (hηb i) (hJ1 i τ hτ x hx)
  obtain ⟨T₀, ι₀, hses₀, c0⟩ := hKer T₁ T₂ F hSur
  have hJY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W Y Mi hi := by
    intro Y ι π hses hY τ i hτ x hx
    rcases (hJmp T₂ Y W.one ι π hses c2 hY hOc τ x).1 hx with h | h
    · exact hJL1 i τ hτ x ((hJmp T₀ T₁ T₂ ι₀ F hses₀ c0 c1 c2 τ x).2 (Or.inr h))
    · rw [hOne.2.1 τ x h]
      simp
  have hQ1 := (hQ d T₁ T₂ F b S η m Mi hi hS' hJL1).2
  set N := eWA PD.p (Hmax n Mi hi) with hN
  have hK : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → ∀ i : ZMod n,
        Kills W π i (lp W N) ∧ Kills W π i (qp W ^ a) := fun Y ι π hses hY i =>
    ⟨(hQ1 Y ι π hses hY i).2.1, (hQ1 Y ι π hses hY i).2.2⟩

  let I := Module.Free.ChooseBasisIndex O FF
  let bF : Module.Basis I O FF := Module.Free.chooseBasis O FF
  have one := fun j : I => extDataOne_exists W hH hExt hOne hEx hdex h5 h6 h9 hA hζ hOd T₂ c2 Mi hi a N
    hJY hK (g (bF j) : G → T₂.V) (g (bF j)).2
  choose yj zj μj νj hZj hcZj hclj hRelj using one
  let y : FF →ₗ[O] W.DD T₂ := bF.constr O yj
  let z : FF →ₗ[O] W.DD T₂ := bF.constr O zj
  let μ : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => μj j i
  let ν : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => νj j i
  have hyb : ∀ j, y (bF j) = yj j := fun j => bF.constr_basis O yj j
  have hzb : ∀ j, z (bF j) = zj j := fun j => bF.constr_basis O zj j
  have hμb : ∀ i j, μ i (bF j) = μj j i := fun i j => bF.constr_basis O (fun j => μj j i) j
  have hνb : ∀ i j, ν i (bF j) = νj j i := fun i j => bF.constr_basis O (fun j => νj j i) j
  refine ⟨N, y, z, μ, ν, fun f => ?_, fun i f => ?_⟩
  · have hκ : ((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V) ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 (g f).2).1
    have hyf : y f = ∑ j, bF.equivFun f j • yj j := by simp [y, Module.Basis.constr_apply_fintype]
    have hzf : z f = ∑ j, bF.equivFun f j • zj j := by simp [z, Module.Basis.constr_apply_fintype]
    have hpair : ((y f, z f) : W.DD T₂ × W.DD T₂) = ∑ j, bF.equivFun f j • ((yj j, zj j) : W.DD T₂ × W.DD T₂) := by
      rw [hyf, hzf]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hmem : ((y f, z f) : W.DD T₂ × W.DD T₂) ∈ herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂) := by
      rw [hpair]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZj j)
    refine ⟨⟨(y f, z f), hmem⟩, hκ, rfl, ?_⟩
    have hx : (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) =
        ∑ j, bF.equivFun f j • (⟨(yj j, zj j), hZj j⟩ :
          ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hpair
    have hsum : (⟨((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hκ⟩ : ↥(latticeCocycles T₂.L)) =
        ∑ j, bF.equivFun f j • (⟨((g (bF j) : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hcZj j⟩ : ↥(latticeCocycles T₂.L)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      conv_lhs => rw [← bF.sum_equivFun f]
      rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    show W.clK T₂ (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) = _
    rw [hx, map_sum, hsum]
    simp only [map_smul, hclj, ← Submodule.mkQ_apply, map_sum]
  · let sA : LetA O n → (W.DD T₂ →ₗ[O] W.DD T₂) := fun c =>
      ((c • LinearMap.id : W.DD T₂ →ₗ[LetA O n] W.DD T₂)).restrictScalars O
    have hsA : ∀ c x, sA c x = c • x := fun c x => by
      simp only [sA, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hNs : ∀ (c : O) (x : W.DD T₂), x ∈ W.N T₂ → c • x ∈ W.N T₂ := fun c x h => by
      rw [← algebraMap_smul (LetA O n) c x]; exact (W.N T₂).smul_mem _ h
    have hJs : ∀ (c : O) (x : W.DD T₂), x ∈ pullJ W T₂ (i - 1) 1 → c • x ∈ pullJ W T₂ (i - 1) 1 :=
      fun c x h => by rw [← algebraMap_smul (LetA O n) c x]; exact Submodule.smul_mem _ _ h
    let Φ4 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ y) + (W.φD T₂ ∘ₗ μ (i - 1)) - μ i
    have hΦ4 : ∀ f', Φ4 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f') + W.φD T₂ (μ (i - 1) f') -
        μ i f' := fun f' => by
      simp only [Φ4, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
    have hΦ4b : ∀ j, Φ4 (bF j) = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • yj j) +
        W.φD T₂ (μj j (i - 1)) - μj j i := fun j => by rw [hΦ4, hyb, hμb, hμb]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (μ i) (fun j => by rw [hμb]; exact (hRelj j i).1) f
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (ν i) (fun j => by rw [hνb]; exact (hRelj j i).2.1) f
    · let Φ3 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ z) + ((W.γ T₂) ∘ₗ μ i - μ i)
      have hΦ3 : ∀ f', Φ3 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f') +
          (W.γ T₂ (μ i f') - μ i f') := fun f' => by
        simp only [Φ3, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ3]
      exact extData_lin (InPN W T₂ 1) ⟨0, (W.N T₂).zero_mem, fun δ _ => map_zero _, (smul_zero _).symm⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ c hx)
        bF Φ3 (fun j => by rw [hΦ3, hzb, hμb]; exact (hRelj j i).2.2.1) f
    · have := extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF (sA (qp W ^ Mi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · have := extData_lin (fun x => ∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T₂ (i - 1) 1)
        ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
        (fun x y ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => ⟨s₁ + s₂, by
          simp only [smul_add, pow_add, mul_smul]
          rw [smul_comm (((PD.p : ℕ) : O) ^ s₁) (((PD.p : ℕ) : O) ^ s₂) x]
          exact Submodule.add_mem _ (hJs _ _ h₁) (hJs _ _ h₂)⟩)
        (fun c x ⟨s₀, h₀⟩ => ⟨s₀, by rw [smul_comm]; exact hJs c _ h₀⟩)
        bF (sA (qp W ^ hi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · let Φ6 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • ν i - sA (qp W ^ a) ∘ₗ μ i
      have hΦ6 : ∀ f', Φ6 f' = ((PD.p : ℕ) : O) ^ N • ν i f' - qp W ^ a • μ i f' := fun f' => by
        simp only [Φ6, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ6]
      exact extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF Φ6 (fun j => by rw [hΦ6, hνb, hμb]; exact (hRelj j i).2.2.2.2.2) f

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FamilyStatementsLocal
section
noncomputable section

namespace Formalism.MainNotions.FamilyNumericLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Filter Topology

def kF (c : ℝ) : ℝ := (1 + Real.exp (-(c * Real.log 6))) / (1 - Real.exp (-(c * Real.log 6)))

theorem exp_neg_log_six_lt_one {c : ℝ} (hc : 0 < c) : Real.exp (-(c * Real.log 6)) < 1 := by
  have h6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  exact Real.exp_lt_one_iff.mpr (by nlinarith)

theorem kF_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ kF c := by
  have h := exp_neg_log_six_lt_one hc
  have h0 := Real.exp_pos (-(c * Real.log 6))
  unfold kF
  exact div_nonneg (by linarith) (by linarith)

theorem kF_mul {c : ℝ} (hc : 0 < c) : kF c * (1 - Real.exp (-(c * Real.log 6))) = 1 + Real.exp (-(c * Real.log 6)) := by
  have h := exp_neg_log_six_lt_one hc
  unfold kF
  field_simp [show (1 - Real.exp (-(c * Real.log 6))) ≠ 0 by linarith]

theorem cyl_univ (D : D7) (k : Fin 2) : cyl D k Set.univ = Set.univ := by
  ext t; simp [cyl]

theorem locShare_nonneg (D : D7) (eV : VecAt D) (CL : ℝ) (hL : lawL D eV CL) (k : Fin 2) (S : Finset (Tup D k)) :
    0 ≤ locShare D eV k S :=
  Finset.sum_nonneg fun t _ => Finset.prod_nonneg fun v _ => (hL k v).1 (t v)

end Formalism.MainNotions.FamilyNumericLemmas
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FirstFrameStepImplication
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def KapPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → kapPiR D HW

def FirstFrameHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → u1R D HW

end Formalism.MainNotions.N.Ln34

end
end

