import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexHeckeConjugatePlacePeterssonAdjoint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ComplexHeckeAdjoint

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

theorem levChi_one {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
  intro k _
  have h1 : ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi (rTup (R.βW i) (R.datWp i R.triv) (Lev.finE (Wc D i) k)) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h1]
  simp [LevCh.datWp, datY]

theorem conj_eq {D : D7} {P P' : PlE D.host} (h : Formalism.BasicNotions.IsConjPl D.host P P') : P' = Formalism.DivisionValues.conjPl P := by
  have hc : ∀ y : 𝓞 D.host.E, Formalism.HermitianLattices.Ext.L3.conjO D.host.E y = Formalism.DivisionValues.cO D.host.E y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO, Formalism.HermitianLattices.Ext.L3.conjO_coe])
  have hcc : ∀ y : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E y) = y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO])
  rw [GlobalTheory.ConjPlaceOff.isConjPl_iff] at h
  ext x
  show x ∈ P'.asIdeal ↔ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    refine ⟨Formalism.DivisionValues.cO D.host.E x, (h _).2 ?_, hcc x⟩
    rwa [hc, hcc]
  · rintro ⟨y, hy, rfl⟩
    rw [← hc]
    exact (h y).1 hy

open GlobalTheory.HeckeParts in

theorem keep_adj {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    {L : LevDat D.host.E ℂ V.rank} (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P)
    (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)}
    (hU : U = Mult θ M (levS V β L) (levChi V β L)) {ip : MMap M → MMap M → ℂ} {c : ℂ}
    (hip : ∀ T T', ip T T' = c * ipM M μ 𝓕 T T') (h : HM.Is U ip) {x : GA D V} {A A' : Finset (GA D V)}
    (hA : LocRep (levG V β L) P x A) (hA' : LocRep (levG V β L) P x⁻¹ A') :
    (∀ y, ∃ y', HM.e y' = heckeOn M A (HM.e y)) ∧ (∀ y, ∃ y', HM.e y' = heckeOn M A' (HM.e y)) ∧
      ∀ y z y' z', HM.e y' = heckeOn M A (HM.e y) → HM.e z' = heckeOn M A' (HM.e z) → inner ℂ y' z = inner ℂ y z' := by
  subst hU
  have h' : HM.Is (Mult θ M (levS V β L) (levChi V β L)) fun T T' => c * ipM M μ 𝓕 T T' :=
    ⟨h.1, h.2.1, fun y z => (h.2.2 y z).trans (hip _ _)⟩
  have hmem : ∀ y, HM.e y ∈ Mult θ M (levS V β L) (levChi V β L) := fun y => h.2.1 ▸ LinearMap.mem_range_self _ y
  have keep : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C → ∀ y,
      heckeOn M C (HM.e y) ∈ LinearMap.range HM.e := by
    intro w C hC y
    rw [h.2.1]
    exact hC.mult hβ hP (fun k hk => levG_le_flag hk) (hmem y) (fun v => rInv_of_mem hχ (hmem y) v)
  have lift : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C →
      ∃ t : Module.End ℂ HM.H, ∀ y, HM.e (t y) = heckeOn M C (HM.e y) := by
    intro w C hC
    refine ⟨(LinearEquiv.ofInjective _ h.1).symm.toLinearMap ∘ₗ ((heckeOn M C ∘ₗ HM.e).codRestrict _ (keep hC)),
      fun y => ?_⟩
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ h.1).apply_symm_apply _)
  obtain ⟨t, ht⟩ := lift hA
  obtain ⟨t', ht'⟩ := lift hA'
  refine ⟨fun y => keep hA y, fun y => keep hA' y, fun y z y' z' hy hz => ?_⟩
  obtain rfl : y' = t y := h.1 (hy.trans (ht y).symm)
  obtain rfl : z' = t' z := h.1 (hz.trans (ht' z).symm)
  exact inner_hecke hχ hμ h𝓕 h' le_rfl hA.2 hA'.2 (hA.card hβ hP hA') ht ht' y z

end GlobalTheory.ComplexHeckeAdjoint

namespace GlobalTheory.CxHeckeAdj

set_option maxHeartbeats 1600000 in

theorem hecke_adjoint : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3),
    Rl.Char3 F → ∀ (i : Fin D.R.m) (k : ℕ) (P P' : PlE D.host), IsSplitPl D.host P → IsConjPl D.host P P' →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    Formalism.IndefR.Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal → 1 ≤ k → k ≤ D.R.r →
    ∃ (α α' : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i)) (R R' : Finset (Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i))),
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P k α ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R ∧
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P' k α' ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' R' ∧
      (∀ x, ∃ x', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x)) ∧
      (∀ y, ∃ y', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y)) ∧
      ∀ x y x' y' : (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).H,
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x) →
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y) →
        ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by

  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl F hc i k P P' _hsp hcj hso hso' _h2 _h2' _hk1 hk
  classical
  obtain ⟨c, hβ⟩ := hc.lev.βW i
  have hrk : k ≤ (Formalism.IndefR.Links.Wc D i).rank := by
    rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact hk
  have hoff : ∀ Q : Formalism.L2.DIV.Pl D.host.E, Formalism.IndefR.Bridge.SplitOff Q (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
      GlobalTheory.HeckeParts.OffLevel (Rl.datWp i Rl.triv) (1 ^ c) Q := by
    intro Q hQ
    refine ⟨hQ.1, ?_, ?_⟩
    · rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top
    · intro PP hPP
      have hPP' : PP ∈ Rl.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
      have hS : PP ∈ (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hc.fam.Sb hPP'
      refine ⟨fun h => hQ.2.1 (h ▸ hS), fun h => hQ.2.2 PP hS ?_⟩
      rw [Formalism.L2.Col.conjIdeal_asIdeal]
      refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ Q).isPrime.ne_top fun a ha => ?_
      obtain ⟨a', ha', e⟩ := h a ha
      rw [Formalism.L2.Col.mem_conjP]
      have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
      rwa [this]
  obtain ⟨α, A, A', hα, hA, hA'⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P hso) hrk
  obtain ⟨α₂, B, B', hα₂, -, -⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P' hso') hrk
  have hα₂' : Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) (Formalism.DivisionValues.conjPl P) k α₂ :=
    GlobalTheory.ComplexHeckeAdjoint.conj_eq hcj ▸ hα₂
  obtain ⟨e, ϖ, he, -, -, -⟩ := id hα
  obtain ⟨a, ha, b, hb, hab⟩ := GlobalTheory.SplitHeckeAdj.hecke_conj (Formalism.IndefR.Links.Wc D i) he hα hα₂'
  obtain ⟨Lp, -, -, -, hK⟩ := GlobalTheory.HeckeParts.loc_package hβ (hoff P hso) he
  have hA₂ : Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α₂ A :=
    GlobalTheory.SplitHeckeAdj.isDC_of_mem (Subgroup.inv_mem _ ((hK a).1 ha).1) (Subgroup.inv_mem _ ((hK b).1 hb).1)
      (by rw [hab]; group) hA.2

  obtain ⟨hk1, hk2, hadj⟩ := GlobalTheory.ComplexHeckeAdjoint.keep_adj hβ (hoff P hso) (GlobalTheory.ComplexHeckeAdjoint.levChi_one Rl.toRealDat i)
    (hc.models.νW i).1.1 (hc.models.νW i).2 rfl
    (fun _ _ => rfl) (hc.models.HW i (Formalism.IndefR.Links.sg0 D A3.A)) hA' hA
  exact ⟨α, α₂, A', A, hα, hA'.2, hα₂, hA₂, hk1, hk2, hadj⟩

end GlobalTheory.CxHeckeAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousResI
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

noncomputable section

namespace GlobalTheory.WeilRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

theorem res_mem_Dec {σ : G E' Ω} (hσ : σ ∈ Dec (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Dec (F := E) A := by
  rw [mem_Dec] at hσ ⊢
  refine Eq.trans ?_ hσ
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

theorem res_mem_Ine {σ : G E' Ω} (hσ : σ ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Ine (F := E) A :=
  ⟨res_mem_Dec hσ.1, hσ.2⟩

theorem res_actsAs {q q' n a b : ℕ} (hq : q' = q ^ n) {σ : G E' Ω} (hσ : ActsAs A q' σ a b) :
    ActsAs A q (AlgEquiv.restrictScalars E σ) (n * a) (n * b) := by
  subst hq
  refine ⟨res_mem_Dec hσ.1, fun x hx => ?_⟩
  rw [pow_mul, pow_mul]
  exact hσ.2 x hx

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

def resW {n : ℕ} (hq : normV w' = normV w ^ n) : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalars E (σ : G E' Ω), by
    obtain ⟨a, b, hσ⟩ := σ.2
    exact ⟨n * a, n * b, res_actsAs hq hσ⟩⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)

def resI : Ine (F := E') A →* Ine (F := E) A where
  toFun t := ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun i => (b i : Ω)
  have : Finite S := (Set.finite_range _).to_subtype
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff E' Ω _).mpr ⟨IntermediateField.adjoin E' S,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun σ hσ => hLU ?_⟩
  have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
  have hlin : (AlgEquiv.restrictScalarsHom E σ).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => hσ' _ (IntermediateField.subset_adjoin E' S ⟨i, rfl⟩)
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end GlobalTheory.WeilRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published GlobalTheory.UnitaryBC
open GlobalTheory.CuspRep.LocEx

namespace GlobalTheory.DiscLocEx

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def opD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (o : Op E a) : Module.End ℂ V := (act o).restrict (hV o)

def finPartD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) : Representation ℂ (GL (Fin a) (Af E)) V :=
  GlobalTheory.PRep.sub (finRep E a) V fun k => hV (.fin k)

def locRepD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
  (finPartD hV).comp (locGL E a w)

theorem isSmooth_finPartD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ) :
    IsSmooth (finPartD hV) := fun φ => by
  convert (ha _ φ.2).level using 1
  ext k
  exact Subtype.ext_iff

theorem isSmooth_locRepD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ)
    (w : HeightOneSpectrum (𝓞 E)) : IsSmooth (locRepD hV w) := fun φ =>
  (isSmooth_finPartD hV ha φ).preimage (CuspSub.continuous_locGL w)

theorem exists_scalarD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem nullPart_opD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (o : Op E a) {x : V} (hx : x ∈ nullPart (locRepD hV w) K) : opD hV o x ∈ nullPart (locRepD hV w) K := by
  cases o with
  | fin k =>
    have h1 := nullPart_act _ K (GeneralLinearGroup.map (pLoc E w) k) (nullPart_comm _ K
      (finPartD hV ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
      simp only [locRepD, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        LocUniq.comm_locGL w (map_pLoc_inv_mul w k)]) hx)
    rwa [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
  | cpt k =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem eq_bot_of_fixedD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    {K : Subgroup (GL (Fin a) (w.adicCompletion E))} (hK : IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))))
    {φ : V} (h0 : φ ≠ 0) (hφ : φ ∈ fixed (locRepD hV.stable w) K) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, locRepD hV.stable w g v ∈ W) (h : W ⊓ fixed (locRepD hV.stable w) K = ⊥) : W = ⊥ := by
  have hi := Submodule.map_injective_of_injective V.injective_subtype
  rcases hV.irred ((nullPart (locRepD hV.stable w) K).map V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, nullPart_opD hV.stable w K o hx, rfl⟩) with h1 | h1
  · have h2 : nullPart (locRepD hV.stable w) K = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    exact le_bot_iff.1 (h2 ▸ le_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK W hW h)
  · have h2 : nullPart (locRepD hV.stable w) K = ⊤ := hi (h1.trans (Submodule.map_subtype_top _).symm)
    exact absurd (eq_zero_of_mem_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK hφ (h2 ▸ Submodule.mem_top)) h0

def typePartD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) : Submodule ℂ V where
  carrier := {ψ | (∀ k ∈ L, GeneralLinearGroup.map (pLoc E w) k = 1 → finPartD hV k ψ = ψ) ∧
    ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k h1 h2 => by rw [map_add, hx.1 k h1 h2, hy.1 k h1 h2],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ => zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k h1 h2 => by rw [map_smul, hx.1 k h1 h2],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem typePartD_act {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (w.adicCompletion E))
    (x : V) (hx : x ∈ typePartD hV w L ρ) : locRepD hV w g x ∈ typePartD hV w L ρ := by
  refine ⟨fun k h1 h2 => ?_, fun y => ?_⟩
  · rw [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, LocUniq.comm_locGL w h2, map_mul,
      Module.End.mul_apply, hx.1 k h1 h2]
  · convert hx.2 (y * finGL E a (locGL E a w g)) using 2 with k
    change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
    rw [mul_assoc, mul_assoc, infGL_comm]

theorem finiteDimensional_typePartD (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (hK : IsOpen (K : Set (GL (Fin a) (w.adicCompletion E)))) :
    FiniteDimensional ℂ ↥(typePartD hV.stable w L ρ ⊓ fixed (locRepD hV.stable w) K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ V, cap τ u φ = c • φ := fun τ u =>
    exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w)))
    (hL.inter ((hK.inter (hL.preimage (CuspSub.continuous_locGL w))).preimage (continuous_map_pLoc w))) W ρ hρ c
  refine FiniteDimensional.of_injective ((V.subtype ∘ₗ (typePartD hV.stable w L ρ ⊓
    fixed (locRepD hV.stable w) K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms
      (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w))) ρ c))
    fun v => Submodule.subset_span ⟨hV.aut _ v.1.2, fun k hk => ?_, v.2.1.2, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  have h1 := v.2.1.1 _ (L.mul_mem (L.inv_mem hk.2.2) hk.1) (map_pLoc_inv_mul w k)
  have h2 := mem_fix.1 v.2.2 _ hk.2.1
  have h3 : finPartD hV.stable k v.1 = v.1 := by
    rw [← mul_inv_cancel_left (locGL E a w (GeneralLinearGroup.map (pLoc E w) k)) k, map_mul, Module.End.mul_apply, h1]
    exact h2
  exact congrArg Subtype.val h3

theorem exists_irred_sub (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧
      ∀ g v, f (σ.ρ g v) = locRepD hV.stable w g (f v)) ∧ IsAdmissible σ.ρ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have h0' : (⟨φ, hφ⟩ : V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab (finPartD hV.stable) ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) :=
    isSmooth_finPartD hV.stable hV.aut _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have : FiniteDimensional ℂ (orbSpan φ) := (hV.aut φ hφ).kfin
  refine exists_irred (isSmooth_locRepD hV.stable hV.aut w) ho (eq_bot_of_fixedD hV w hc h0' (mem_fix.2 hK))
    (typePartD hV.stable w (stab (finPartD hV.stable) ⟨φ, hφ⟩) (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)))
    (typePartD_act hV.stable w _ _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ⟨fun k hk _ => hk, ?_⟩, h0'⟩)
    (finiteDimensional_typePartD h hV w hL (isContRep_sub _ _))
  exact AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
    ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩

end GlobalTheory.DiscLocEx

open GlobalTheory.DiscSpec GlobalTheory.SmGL in

theorem GlobalTheory.DiscLocEx.exists_isLocCompGL : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V →
    ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  intro h E _ _ _ N V hV w
  obtain ⟨σ, ⟨f, hf0, hf⟩, -⟩ := GlobalTheory.DiscLocEx.exists_irred_sub h hV w
  refine ⟨σ, V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun g v => congrArg Subtype.val (hf g v)⟩
  exact LinearMap.congr_fun e v
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lagrangian_term_frame_independent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  first | exact @GlobalTheory.RawLift.lagTerm_frame_indep | exact GlobalTheory.RawLift.lagTerm_frame_indep | (intros; apply GlobalTheory.RawLift.lagTerm_frame_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_off_stableSet : ∀ (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : PlE D.host),
    (∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0) → placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)) →
    (∀ Q ∈ Sb, Q ∈ S0) → IsSplitPl D.host P → P ∉ S0 →
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  first | exact @GlobalTheory.ConjPlaceOff.exists_conj_off | exact GlobalTheory.ConjPlaceOff.exists_conj_off | (intros; apply GlobalTheory.ConjPlaceOff.exists_conj_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineCharJumpOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LTChar

theorem exists_crystalline_char_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀
  haveI := (P.PD K).finK₀
  have hn : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  obtain ⟨x, hxu, hxφ, hx1, hx2, hxj⟩ := GlobalTheory.T.exists_cyclotomic_period_local_prime l P AI hT K _ hn
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unramified_character_of_eigen_unit l P K x hxu (GlobalTheory.T.galois_periodRatio_mem_unramified_alt l P AI hT K x hxu hxφ hx1 hx2 hxj)
  have hcont := GlobalTheory.T.continuous_galois_character_of_bcris_unit_fil_one l P AI hT K x hxu hx1 hx2 c hc
  obtain ⟨χ, hχc, hχ⟩ := GlobalTheory.T.exists_continuous_integralUnitChar_of_char l K LL τ₀ c hcont
  exact ⟨χ, hχc, GlobalTheory.T.crystalline_character_jump_one_at_embedding l P AI hT K LL hA τ₀ x hxu hxφ hx1 hx2 hxj c hc _ hχc hχ⟩

end GlobalTheory.LTChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_lattice_periods_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  first | exact @GlobalTheory.SeedExists.exists_seed | exact GlobalTheory.SeedExists.exists_seed | (intros; apply GlobalTheory.SeedExists.exists_seed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRepStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  first | exact @GlobalTheory.TensorFactor.exists_equiv_extTensor | exact GlobalTheory.TensorFactor.exists_equiv_extTensor | (intros; apply GlobalTheory.TensorFactor.exists_equiv_extTensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRhamStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_log_semistable_to_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧ (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  first | exact @GlobalTheory.BstLog.iota_exists | exact GlobalTheory.BstLog.iota_exists | (intros; apply GlobalTheory.BstLog.iota_exists <;> assumption)
end

