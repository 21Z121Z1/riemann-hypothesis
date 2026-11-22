import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0023
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def ExpL (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (ζ : LL) (x : LA W T π' c)
    (f : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m₀ : ℤ, ∀ i < m₀, f i = 0) ∧ ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y ∧
    ∀ i, serMul (W.lev c ζ (Eπ ^ h')) f i = expS W T c ζ (fun j => (a j : LetA O n)) y i

abbrev QL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Type :=
  ↥(LamLA W T π' Eπ h' c ⊤) ⧸ (piNL W T Pt π' Eπ h' c 1).comap (LamLA W T π' Eπ h' c ⊤).subtype

def ModelL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M : ℕ) (c : ZMod n) : Prop :=
  NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ ∧
  (∀ x ∈ NL W T Pt π' Eπ h' c, γLA W T π' c x ∈ NL W T Pt π' Eπ h' c) ∧
  (∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c) ∧
  (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c ∧
  (∀ x ∈ LamLA W T π' Eπ h' c ⊤, ∀ k : ℕ, ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c →
    x ∈ NL W T Pt π' Eπ h' c) ∧
  JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c M ∧
  ∀ x ∈ LamLA W T π' Eπ h' c ⊤, γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c →
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i)

def ModelQ (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  Module.Finite O (QL W T Pt π' Eπ h' c) ∧
    ∀ (a : O) (q : QL W T Pt π' Eπ h' c), a ≠ 0 → a • q = 0 → q = 0

def ModelK {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (π' : LetA O n) (ρ : ℕ) (c : ZMod n) : Prop :=
  ∀ y ∈ NcS W T₂ (c - 1), ∃ x ∈ NcS W T₁ (c - 1), W.map F x - ((PD.p : ℕ) : O) ^ ρ • y ∈ PiNS W T₂ π' 1

end Local

section Record

def modelLR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c

def modelQR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelQ ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def modelKR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T₁.ρ →
      IsCrys ((D.loc l).PD K) T₂.ρ → F.Onto → (∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) → ∀ c, ModelK ((HW l).W K 1 LL hG) F π' (rhoA l (eK K) h') c

end Record

def ModelLStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW

def ModelQStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelQR D HW

def ModelFStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW

def ModelKStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelKR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.Step1KillXList
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section Kill

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def step1Kill_roots (c : ZMod n) (M h a : ℕ) : Finset ℤ :=
  ((jumpSetL W T c M h) ×ˢ Finset.Icc (((0 : ℕ) : ℤ) + 1) (a : ℤ)).image (fun p : ℤ × ℤ => p.1 + p.2)

theorem step1Kill_xList (c : ZMod n) (M h a : ℕ) :
    xListL W T c M h 0 a = (step1Kill_roots W T c M h a).sort (· ≤ ·) := rfl

theorem step1Kill_cO (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hRN : Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) :
    ∃ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) ∧
      cO 0 = 0 ∧ ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ) := by
  classical
  have hc : ∀ j : ℤ, ((PD.p : ℕ) : LL) = 0 → Formalism.MainNotions.CrystallineLiftingInputs.cR W j = 0 := by
    intro j h0
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    simp [h0]
  have hp0 : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h1 := hRN.2 1 0 (by norm_num)
    rw [hc 1 h0, hc 0 h0, sub_zero, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  have hnn : ∀ x : ℤ, 0 ≤ v (Formalism.MainNotions.CrystallineLiftingInputs.cR W x) := by
    intro x
    by_cases hx : x = 0
    · rw [hx, hRN.1, AddValuation.map_zero]
      exact le_top
    · have h := hRN.2 x 0 hx
      rw [hRN.1, sub_zero] at h
      rw [h]
      first
        | exact WithTop.coe_nonneg.mpr (by positivity)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by positivity))
  have hex : ∀ x : ℤ, ∃ o : O, algebraMap O LL o = Formalism.MainNotions.CrystallineLiftingInputs.cR W x := fun x => hV.2.1 _ (hnn x)
  refine ⟨fun x => Classical.choose (hex x), ?_, ?_, ?_⟩
  · intro x
    apply hV.1
    rw [map_mul, map_natCast, Classical.choose_spec (hex x), map_sub, map_one]
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    first
      | (rw [div_neg, mul_neg, mul_div_assoc', mul_div_cancel_left₀ _ hp0, neg_sub])
      | (field_simp; ring)
      | field_simp
  · apply hV.1
    rw [Classical.choose_spec (hex 0), hRN.1, map_zero]
  · intro x hx
    have h := hRN.2 x 0 hx
    rw [hRN.1, sub_zero] at h
    rw [Classical.choose_spec (hex x), h]
    first
      | exact WithTop.coe_natCast _
      | (norm_cast; done)
      | (simp; done)
      | (push_cast; rfl)

theorem step1Kill_kill [NeZero n] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hDS : DerivationPreservesQLattice W)
    (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (Mi hi : ZMod n → ℕ)
    (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi) (c : ZMod n) (cO : ℤ → O)
    (hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) (hc0 : cO 0 = 0)
    (a : ℕ) {y₀ : W.DD T} (hy : QLattice W T c a y₀) :
    Polynomial.aeval (derivationOnWachModule W T)
      (X * ∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀ ∈ W.N T := by
  have hU := hR.πU
  have hπΔ := hR.πΔ
  have hv : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1 := by
    rw [map_sub, map_one, W.gam_gen, hA.2.1]
    simp
  have hyNl : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ ∈ W.Nl T c := by
    have h1 : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ = (letE c : LetA O n) • (Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀) := by
      rw [smul_smul, mul_comm, ← smul_smul, hy.1.1]
    rw [h1]
    exact Formalism.MainNotions.LiftingTheory.liftb_letE_mem W T c hy.2
  obtain ⟨seq, h0, hstep, hN⟩ := hD hA T Mi hi hT hJ (W.χΓ W.gam) rfl hv cO hcO c 0 a y₀
    (Nat.zero_le a) hyNl hy.1.2
  have hseq := Formalism.MainNotions.LiftingTheory.lifta_seq W T (uniformizerInverse W) (algebraMap_uniformizer_mul_inverse hU) cO _ seq hstep
  rw [h0] at hseq
  have hNs : seq (xListL W T c (Mi c) (hi c) 0 a).length ∈ W.N T :=
    Formalism.MainNotions.LiftingTheory.liftb_Nl_le W T c (by simpa using hN)
  rw [hseq] at hNs
  have hprod : ((xListL W T c (Mi c) (hi c) 0 a).map
      fun x => (X - C (cO x) : Polynomial O)).prod =
      ∏ x ∈ step1Kill_roots W T c (Mi c) (hi c) a, (X - C (cO x)) := by
    rw [step1Kill_xList, ← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rw [hprod, ← Finset.prod_filter_mul_prod_filter_not _ (fun x => x ≠ 0)] at hNs
  by_cases h0m : (0 : ℤ) ∈ step1Kill_roots W T c (Mi c) (hi c) a
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, not_not]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨h0m, rfl⟩
    rw [hf, Finset.prod_singleton, hc0, map_zero, sub_zero, mul_comm] at hNs
    exact hNs
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, not_not, iff_false, not_and]
      rintro hx rfl
      exact h0m hx
    rw [hf, Finset.prod_empty, mul_one] at hNs
    rw [map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    have hQ : QLattice W T c 0 (Polynomial.aeval (derivationOnWachModule W T)
        (∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀) :=
      ⟨invariantLetter_polynomial_derivation W T hπΔ hU _ hy.1, by simpa [derivationOnWachModule] using hNs⟩
    simpa using (qLattice_derivation W T hDS hA hT c 0 hQ).2

theorem step1Kill_norm (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hvp : v (PD.p : LL) = 1) (cO : ℤ → O)
    (hcv : ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ))
    (Sx : Finset ℤ) (hS0 : (0 : ℤ) ∉ Sx) (s : ℕ) (hs : ∑ x ∈ Sx, padicValInt PD.p x ≤ s) :
    ∃ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = ((PD.p : ℕ) : O) ^ s := by
  classical
  have hcoef : ∀ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = w * ∏ x ∈ Sx, -(cO x) := by
    intro w
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  have hval : ∀ S : Finset ℤ, (0 : ℤ) ∉ S →
      v (algebraMap O LL (∏ x ∈ S, -(cO x))) = ((∑ x ∈ S, padicValInt PD.p x : ℕ) : WithTop ℚ) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simp
    · intro a S ha ih h0
      have ha0 : a ≠ 0 := fun h => h0 (by rw [← h]; exact Finset.mem_insert_self a S)
      have hS0' : (0 : ℤ) ∉ S := fun h => h0 (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, AddValuation.map_mul, map_neg,
        AddValuation.map_neg, hcv a ha0, ih hS0', Nat.cast_add]
  have hvc := hval Sx hS0
  have hc0 : algebraMap O LL (∏ x ∈ Sx, -(cO x)) ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hvc
    exact WithTop.natCast_ne_top _ hvc.symm
  have hvps : v (((PD.p : ℕ) : LL) ^ s) = ((s : ℕ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hvp, nsmul_one]
  have aux : ∀ r : WithTop ℚ, r + ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : WithTop ℚ) = ((s : ℕ) : WithTop ℚ) →
      0 ≤ r := by
    intro r hr
    induction r using WithTop.recTopCoe with
    | top => exact le_top
    | coe q =>
      rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_inj] at hr
      have hq : ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs
      first
        | exact WithTop.coe_nonneg.mpr (by linarith)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by linarith))
  have hw'0 : 0 ≤ v (((PD.p : ℕ) : LL) ^ s / algebraMap O LL (∏ x ∈ Sx, -(cO x))) := by
    apply aux
    rw [← hvc, ← AddValuation.map_mul, div_mul_cancel₀ _ hc0, hvps]
  obtain ⟨w, hw⟩ := hV.2.1 _ hw'0
  refine ⟨w, ?_⟩
  rw [hcoef]
  apply hV.1
  rw [map_mul, hw, div_mul_cancel₀ _ hc0, map_pow, map_natCast]

end Kill

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.StrictSesLetter
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.Strict

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

section Funct

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (f : V →ₗ[LL] V')

theorem ιV_crisMap (z : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V') (crisMap B f z) = crisMap BdR f (ιV PD (LL := LL) (V := V) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [crisMap, ιV]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crisMap_mulVB (c : K₀) (z : V ⊗[Qp] B) :
    crisMap B f (mulVB (LL := LL) (V := V) (B := B) c z) = mulVB (LL := LL) (V := V') (B := B) c (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [crisMap, mulVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_DcrisL_iff (τ₀ : K₀ →ₐ[Qp] LL) (z : V ⊗[Qp] B) :
    z ∈ DcrisL PD ρ τ₀ ↔ z ∈ Dcris PD ρ ∧ ∀ c : K₀, mulVB (LL := LL) (V := V) (B := B) c z = τ₀ c • z := by
  simp [DcrisL, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

end Funct

section SES

variable {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def StrictOne (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L), IsSESLat (Qp := Qp) ι π →
    IsCrys PD T₂.ρ → IsCrys PD Y.ρ → ∀ u : ℤ,
      (FilCris PD Y.ρ u).comap (crisMap B ι.f) ⊓ Dcris PD T₂.ρ = FilCris PD T₂.ρ u

end SES

section P4Y

variable {PD} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end P4Y

section Rec

theorem p4YL (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.ArcLiftingSetup.AtCaseA fun l _ K LL hG => Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  exact hL l K LL hCA h5

end Rec

end Formalism.MainNotions.UnusedSlot80.Strict

end
end

