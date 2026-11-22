import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleThreePrime
section
noncomputable section

namespace Formalism.MainNotions.AdmissibleThreePrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def TheoremThreePrime (D : D7) : Prop := ArithmeticCylinders.TheoremThreePrime D

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

def LabelDegreeHypotheses (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)),
    (∃ x, HasParamX D.nd D.naut i x Sig) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
        (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
          (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
        Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
              (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
            fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
        ∃ φ : G D.host.E D.nd.Om,
          redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k) ∧
      (∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
          (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
          (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
            (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
          Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
            ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
                (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
              fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
          D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
            ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂)

def Adm3p (D : D7) : Prop := SumRepresentations.tieLab D ∧ LabelDegreeHypotheses D

def ThreePrimeTheorem (D : D7) : Prop := Adm3p D → TheoremThreePrime D

def PlaceLawConstantSix {D : D7} (A : ArithmeticCylinders.AllRows D) : Prop := ArithmeticCylinders.PlaceLawIdempotents A 6

def GLarge (D : D7) : Prop := ∀ k : Fin 2, 2 * D.R.r ≤ D.host.g k

def VecData {D : D7} (A : ArithmeticCylinders.AllRows D) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), ∃ ψ₀ : AddChar (ZMod (D.host.g k)) ℂ, ψ₀ ≠ 1 ∧
    (A.eVec k v = ArithmeticCylinders.eUk D k ψ₀ ∨ A.eVec k v = ArithmeticCylinders.eJk D k ψ₀)

def AdmCylindersL {D : D7} (A : ArithmeticCylinders.AllRows D) : Prop := ArithmeticCylinders.ConclusionL D ∧ GLarge D ∧ VecData A

def PlaceLawTheorem {D : D7} (A : ArithmeticCylinders.AllRows D) : Prop := AdmCylindersL A → PlaceLawConstantSix A

theorem place_law_theorem_holds {D : D7} (A : ArithmeticCylinders.AllRows D) : PlaceLawTheorem A :=
  fun ⟨hL, hg, hV⟩ => ArithmeticCylinders.place_law_of_statement A hL hg hV

theorem place_law_idempotents_six_of_lifting {D : D7} (A : ArithmeticCylinders.AllRows D) (hS : ArithmeticCylinders.LiftingLemmasStatement D) (hq : ArithmeticCylinders.admLq D) (hg : GLarge D)
    (hV : VecData A) : ArithmeticCylinders.PlaceLawIdempotents A 6 :=
  place_law_theorem_holds A ⟨hS hq, hg, hV⟩

end Formalism.MainNotions.AdmissibleThreePrime
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CurveIdealTorusProperties
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.BlochKatoReduction

namespace Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X)

theorem partA_of_partAT (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) (h : partAT bkP i Q k' ψ' eps') :
    partA bkP i Q k' ψ' eps' := by
  obtain ⟨epsT, h0, hs, hb⟩ := h
  unfold partA
  calc ∑ s ∈ SigG bkP i, sLen bkP i s k' Q (psiAt (X.side i s) (ψ'.comp (X.art i Q)))
      ≤ ∑ s ∈ SigG bkP i, ENNReal.ofReal ((nu X i : ℝ) + epsT s) :=
        Finset.sum_le_sum (fun s hs' => hb s ((mem_SigG bkP i s).1 hs'))
    _ = ENNReal.ofReal (∑ s ∈ SigG bkP i, ((nu X i : ℝ) + epsT s)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun s _ => add_nonneg (Nat.cast_nonneg _) (h0 s))).symm
    _ ≤ ENNReal.ofReal (eps' + (nu X i : ℝ) * (SigG bkP i).card) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        linarith

def ReducedLevelRaisingAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partAT bkP i Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def ReducedMainClauses (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partAT bkP i Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def ReducedBaseClausesAt (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partAT bkP i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

end Gen

variable (D : Formalism.BasicNotions.D7)

def CurveIdealTorusProperties (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.ReducedLevelRaisingAt (pin bkP) N0 i

def ReducedMainClausesAll (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.ReducedMainClauses (pin bkP) N0 i

def ReducedBaseClauses (bkP : BK D) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.ReducedBaseClausesAt (pin bkP) i

end Formalism.MainNotions.BlochKatoReduction

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JInvJumpGen
section
noncomputable section

namespace Formalism.MainNotions.N.JsetEmb

open Formalism.WeaklyAdmissibleFiltrations Module Polynomial TensorProduct

section Inv

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem inv_one_mem_all (h1 : (1 : BdR) ∈ PD.Fil 1) : ∀ a : ℤ, (1 : BdR) ∈ PD.Fil a := by
  have hpos : ∀ n : ℕ, (1 : BdR) ∈ PD.Fil ((n : ℤ) + 1) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      have := PD.Fil_mul 1 ((n : ℤ) + 1) 1 1 h1 ih
      rw [one_mul] at this
      convert this using 2
      push_cast; ring
  have hle : ∀ (a : ℤ) (n : ℕ), PD.Fil (a + n) ≤ PD.Fil a := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      apply ih
      have hx' : x ∈ PD.Fil (a + n + 1) := by
        have e : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
        rwa [e] at hx
      exact PD.Fil_anti (a + n) hx'
  intro a
  rcases le_or_gt a 1 with h | h
  · have e : (1 : ℤ) = a + ((1 - a).toNat : ℕ) := by omega
    have := hle a (1 - a).toNat
    rw [← e] at this
    exact this h1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, a = (n : ℤ) + 1 := ⟨(a - 1).toNat, by omega⟩
    rw [hn]; exact hpos n

theorem field_inter_filtration_one_eq_zero (c : K) (hc : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hne
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ hc
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne, map_one] at this
  have hall := inv_one_mem_all PD h1
  have h0 : (1 : BdR) = 0 := PD.Fil_sep 1 hall
  apply PD.not_mem_filtration_two
  have : PD.ι PD.t = 0 := by
    rw [← one_mul (PD.ι PD.t), h0, zero_mul]
  rw [this]
  exact (PD.Fil 2).zero_mem

def invPsi (φ : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift ((LinearMap.lsmul Qp BdR).compl₁₂ φ LinearMap.id)

end Inv

end Formalism.MainNotions.N.JsetEmb

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
section
noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

def DeltaInvariantNormBound (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  WachLatticeFreeGlobal D HW F ∧ P2 D HW F ∧ P3 D HW F C ∧ P4 D HW F C ∧ P5 D HW F ∧ P6 D HW F ∧ P7 D HW F ∧
    P8 D HW F ∧ P9 D HW F ∧ WachCharacterisation D HW F ∧ gammaSemisimpleQuotientGlobal D HW F ∧ Pr2a D HW F ∧ Pr2b D HW F ∧ Pr2c D HW F ∧
    Pr2d D HW F ∧ lem3 D HW F ∧ ConclusionE D HW F

def DeltaInvariantLatticeCriterion {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop :=
  WachLatticeFree W ∧ P2W W ∧ P3W W ∧ P4W W Pt ∧ P5W W ∧ WachSaturationExactness W ∧ WachCrystallineExtension W ∧ WachMaxJumpBound W ∧ P9W W ∧ WachCharacterisationLattice W

def deltaInvariantLatticeLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (F : FonOf LT AI HW) (_C : CmpOf LT AI HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    DeltaInvariantLatticeCriterion ((HW l).W K s LL h) (ptK LT HW h)

def deltaInvariantLatticeGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  deltaInvariantLatticeLocal D.loc HW D.locA F C

theorem thm1used_of {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    {C : CmpOf D.loc D.locA HW F} (h : thm1 D HW F C) : deltaInvariantLatticeGlobal D HW F C :=
  fun l _ K s LL g => ⟨(h l K s LL g).1.1, (h l K s LL g).2.1, (h l K s LL g).2.2.1,
    (h l K s LL g).2.2.2.1, (h l K s LL g).2.2.2.2.1, (h l K s LL g).2.2.2.2.2.1,
    (h l K s LL g).2.2.2.2.2.2.1, (h l K s LL g).2.2.2.2.2.2.2.1, (h l K s LL g).2.2.2.2.2.2.2.2.1,
    (h l K s LL g).2.2.2.2.2.2.2.2.2.1⟩

def UsedLocalConclusion (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  deltaInvariantLatticeGlobal D HW F C ∧ gammaSemisimpleQuotientGlobal D HW F ∧ prop2 D HW F ∧ lem3 D HW F

section Guard

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def ClKNatG (W : LocWach PD LL O v n) : Prop := (PD.p = 2 → ∃ i : K, i ^ 2 = -1) → W.ClKNat

end Guard

def ClKNatGL (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ClKNatG ((HW l).W K s LL h)

end Formalism.MainNotions.DeltaInvariantLattices
end
end

