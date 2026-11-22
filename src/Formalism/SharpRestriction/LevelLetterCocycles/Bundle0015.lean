import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusIterateUniformizerUnitProducts
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section F2Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def unitQProds : Submonoid (LetA O n) where
  carrier := {f | ∃ (u : (LetA O n)ˣ) (J : Multiset ℕ), f = (u : LetA O n) * (J.map fun j => (W.φA ^ j) W.Q).prod}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨u, J, rfl⟩ ⟨u', J', rfl⟩
    refine ⟨u * u', J + J', ?_⟩
    rw [Multiset.map_add, Multiset.prod_add, Units.val_mul]
    ring

theorem ps_mem_unitQProds (hs : W.s = 1) (hq : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)))
    (s : ℕ) : (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨w, hw⟩ := hq
  have hQ : W.Q = W.q := by
    simp [LocWach.Q, hs]
  have e : W.π₀ + ((PD.p : ℕ) : LetA O n) = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.Q := by
    rw [hQ, hw, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨Units.map ((W.φA ^ s : LetA O n →ₐ[O] LetA O n) : LetA O n →* LetA O n) w⁻¹, {s}, ?_⟩
  rw [e, map_mul]
  simp

theorem pi0pow_mem_aN (T : LocLat G Qp LL O) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (x : W.DD T) (hx : x ∈ W.N T) :
    W.π₀ ^ M • x ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
  obtain ⟨w, hw⟩ := hπ
  refine ⟨((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) • x, (W.N T).smul_mem _ hx, ?_⟩
  have e : W.π₀ ^ M = letπ * ((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) := by
    rw [hw, mul_pow, ← pow_mul]
    have : (PD.p - 1) * M = ((PD.p - 1) * M - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [e]
  simp only [mul_smul]

theorem restriction_eq_restriction_H1 (H : Subgroup G) (T : LocLat G Qp LL O) (κ : LatticeCohomology T.L) :
    Formalism.MainNotions.DeltaInvariantLattices.res H T κ = resH1 T H κ := rfl

theorem wach_cocycle_class_mem_latticeFiniteCohomology (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr')
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (x : ↥(W.wachCocyclesDelta T)) (hz : ∃ z' ∈ W.NΔ T, (x : W.DD T × W.DD T).2 = W.π₀ ^ M • z')
    (Λ : LetA O n) (hΛ : Λ ∈ unitQProds W) (hy : Λ • (x : W.DD T × W.DD T).1 ∈ W.N T) :
    W.clK T x ∈ latticeFiniteCohomology PD T.L := by
  have hg : W.gamK = W.gam := W.gamK_eq_one hs hp
  have hr := ((h9 T hT hs hp).2.2 hfr).1
  obtain ⟨_, _, hπ, _, hq, _⟩ := hr
  have hq' : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)) := by
    obtain ⟨w, hw⟩ := hq
    refine ⟨w, ?_⟩
    rw [hw]
    congr 1
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]
  have hmem : (x : W.DD T × W.DD T) ∈ W.divisibleCocycles T := by
    have h1 := (Submodule.mem_inf.mp x.2).1
    rw [hg] at h1
    exact h1
  rw [h2b T hT, restriction_eq_restriction_H1, hres T x ⟨_, hmem⟩ rfl]
  obtain ⟨u, J, rfl⟩ := hΛ
  obtain ⟨z', hz', hzz⟩ := hz
  have hy' : (J.map fun j => (W.φA ^ j) W.Q).prod • (x : W.DD T × W.DD T).1 ∈ W.N T := by
    have := (W.N T).smul_mem ((u⁻¹ : (LetA O n)ˣ) : LetA O n) hy
    rwa [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  have hzN : (x : W.DD T × W.DD T).2 ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
    rw [hzz]; exact pi0pow_mem_aN W T M hM hπ z' hz'.1
  have := h7 T hT J (x : W.DD T × W.DD T).1 (x : W.DD T × W.DD T).2 hy' hzN hmem
  exact this

theorem frobenius_iterate_uniformizer_unit_products (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (s : ℕ) :
    (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨_, _, _, _, hq, _⟩ := ((h9 T hT hs hp).2.2 hfr).1
  refine ps_mem_unitQProds W hs ?_ s
  obtain ⟨w, hw⟩ := hq
  refine ⟨w, ?_⟩
  rw [hw]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]

end F2Core

section F2Rows

theorem caseA_of_le_Kur_of_ne_two {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) {K LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x, x.2, hK x.2⟩, rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p]
  exact hl

theorem finrank_of_caseA {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) :
    Module.finrank K₀ K = 1 := by
  have e : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1
  rw [← e.finrank_eq, Module.finrank_self]

end F2Rows

section F2At

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem wach_cohomology_class_unramified_functor (hC : Formalism.MainNotions.LiftingTheory.CaseA W) (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.WachCoordinates.F2 W := by
  intro hh M hM T hT _ c x hx hΛ
  have hfr := finrank_of_caseA W hC
  obtain ⟨Λ, ⟨k, m, rfl⟩, hΛy⟩ := hΛ
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b hres T hT M (by omega) x hx.2.2 _ ?_ hΛy.1
  exact Submonoid.prod_mem _ fun s _ => pow_mem (frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s) _

theorem wach_cohomology_class_at_functor (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : W.gamK = W.gam → ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.ArcLiftingSetup.SecondWachFiltration W := by
  intro hC hh M hM T hT _ c y x Λ hΛ _ hΛy hcls
  have hfr := finrank_of_caseA W hC
  obtain ⟨z, hc, hz, rfl⟩ := hcls
  obtain ⟨y', hy', _, hyy⟩ := hΛy
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b (hres (W.gamK_eq_one hC.2.1 hC.2.2))
    T hT M (by omega) ⟨(y, z), hc⟩ hz Λ ?_ ?_
  · refine (Submonoid.closure_le.mpr ?_) hΛ
    rintro _ ⟨s, rfl⟩
    exact frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s
  · show Λ • y ∈ W.N T
    rw [hyy, one_smul]
    exact hy'.1

end F2At

section F2Rows2

theorem wach_cohomology_class_unramified_case (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationEtale D HW F := fun l _ K LL hA _ =>
  wach_cohomology_class_unramified_functor ((HW l).W K 1 LL hA.2.2) (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1)
    (h.1 l K 1 LL hA.2.2) (h.2.1 l K 1 LL hA.2.2) (h.2.2 l K 1 LL hA.2.2)
    (((F l).E K 1 LL hA.2.2).tie.clK_res
      (((HW l).W K 1 LL hA.2.2).gamK_eq_one (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.1
        (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.2))

theorem cohomology_class_unramified_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : FamilyMassExplicitOfVolumeAgreement D HW F :=
  fun h => wach_cohomology_class_unramified_case D HW F h.1

theorem second_filtration_case_a_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationArcLifting D HW F := fun l _ K LL hG _ _ =>
  wach_cohomology_class_at_functor ((HW l).W K 1 LL hG) (h.1 l K 1 LL hG) (h.2.1 l K 1 LL hG) (h.2.2 l K 1 LL hG)
    ((F l).E K 1 LL hG).tie.clK_res

theorem second_filtration_theorem_arc_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : SecondFiltrationTheoremArcLifting D HW F :=
  fun h => second_filtration_case_a_of_hypotheses D HW F h.1

end F2Rows2

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
section
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def H0FixedPoints (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, Nonempty (↥(invariantLattice T) ≃ₗ[O] ↥(fixDD W T))

def FontCore (W : LocWach PD LL O v n) : Prop :=
  (∀ (T T' : LocLat G Qp LL O) (f : W.DD T →ₗ[W.EE] W.DD T'),
    (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) →
      ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x) ∧
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := Qp) (O := O) ι π →
    Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
      ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) ∧
  (∃ ψ : W.EE →ₗ[O] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧
    (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧
    (∀ j < PD.p, ∀ a, ψ (algebraMap (LetA O n) W.EE (1 + letπ) ^ j * W.φE a) = if j = 0 then a else 0) ∧
    ∀ x, ∃ c : Fin PD.p → W.EE, x = ∑ j : Fin PD.p, algebraMap (LetA O n) W.EE (1 + letπ) ^ (j : ℕ) * W.φE (c j)) ∧
  ∀ T : LocLat G Qp LL O, ∃ ψ : W.DD T →ₗ[O] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧
    (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x)

theorem herrLat_iff (W : LocWach PD LL O v n) : HerrLat W ↔
    (∀ T : LocLat G Qp LL O, Function.Surjective (W.clK T) ∧
      ∀ p, W.clK T p = 0 ↔ ∃ m : W.DD T, (∀ δ ∈ W.DelF, W.γD T δ m = m) ∧
        (p : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) ∧
    W.ClKNat ∧ H0FixedPoints W ∧ FontCore W := Iff.rfl

end Core

def H0InvariantsUnramified (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), H0FixedPoints ((HW l).W K 1 LL hA.2.2)

def FieldOfNormsSequence (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrComplexNaturality.FN D HW F

def H0InvariantsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FieldOfNormsSequence D HW F → H0InvariantsUnramified D HW F

def LitFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), FontCore ((HW l).W K 1 LL hA.2.2)

def HerrLatticeDescription (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm16 D HW F

def HerrLatticeHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F ∧ H0InvariantsUnramified D HW F ∧ LitFont D HW F

def HerrLatticeTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrLatticeHypotheses D HW F → HerrLatticeDescription D HW F

theorem herr_lattice_of_fon (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeTheorem D HW F := by
  rintro ⟨h, h0, hF⟩ l _ K LL hA
  have h1 := (h l K 1 LL hA.2.2).1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
  refine (herrLat_iff _).2 ⟨fun T => ⟨(h1 T).1, (h1 T).2.1⟩, ?_, h0 l K LL hA, hF l K LL hA⟩
  intro T T' f pr pr' hp
  exact ((h1 T).2.2 T' f pr pr' hp).symm

def LitSub (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), HerrSub ((HW l).W K 1 LL hA.2.2)

def HerrExtensionEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
    Formalism.MainNotions.tableLineDegreeTwo.HerrExt ((HW l).W K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie

def AdmExtT (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrComplexNaturality.FN D HW F ∧ Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F

def HerrExtensionEtaleTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtT D HW F → HerrExtensionEtale D HW F

def HerrLatticeFurtherConditions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm17 D HW F

theorem herr_lattice_rest_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeFurtherConditions D HW F ↔ LitSub D HW F ∧ HerrExtensionEtale D HW F :=
  ⟨fun H => ⟨fun l _ K LL hA => (H l K LL hA).1, fun l _ K LL hA => (H l K LL hA).2⟩,
    fun H l _ K LL hA => ⟨H.1 l K LL hA, H.2 l K LL hA⟩⟩

def SenOperatorLetter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm21 D HW F

def SenOperatorTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm → SenOperatorLetter D HW F

end Formalism.MainNotions.InvariantsGenerators
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.KillerSecondTheoremHolds
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem killer_first_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C : ℝ} (hC : 8 ≤ C) :
    KillerWithConstantTheorem D HW F C := by
  intro hA
  obtain ⟨hL, hP⟩ := hA
  exact Formalism.MainNotions.ArcLiftingSetup.pi_stability_content_clause D HW F hC hL (fun l _ K LL hG hc h5 =>
    hP l K LL hc h5 ((HW l).W K 1 LL hG).gam)

theorem killer_second_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : KillerWachCoordinatesTheorem D HW F := by
  intro hP
  exact Formalism.MainNotions.WachCoordinates.killer_conditions_of_stable D HW F hP

theorem root_multiplicity_two (D : D7) : RootMultiplicityTwo D :=
  Formalism.MainNotions.ArcLiftingSetup.content_divisibility_clause D

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LamPS
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def letS (c : ZMod n) : Submodule O (W.DD T) :=
  LinearMap.ker ((((letE c : LetA O n) • LinearMap.id - LinearMap.id :
    W.DD T →ₗ[LetA O n] W.DD T)).restrictScalars O)

def DelS : Submodule O (W.DD T) :=
  ⨅ δ ∈ W.DelF, LinearMap.ker (W.γD T δ - LinearMap.id)

def NcS (c : ZMod n) : Submodule O (W.DD T) :=
  (W.N T).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def PcS (c : ZMod n) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  ((Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).comap (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (Eπ ^ h'))).restrictScalars O ⊓
    DelS W T ⊓ letS W T c

def PiNS (π' : LetA O n) (k : ℕ) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ k)).restrictScalars O ⊓ DelS W T

def InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  LamPS W T Eπ h' c ⊓ (PiNS W T π' k).comap (W.γD T W.gamK - LinearMap.id)

abbrev JcQ (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Type :=
  ↥(InvS W T π' Eπ h' M c) ⧸ (PiNS W T π' M).comap (InvS W T π' Eπ h' M c).subtype

abbrev IcQ (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Type :=
  ↥(InvS W T π' Eπ h' 1 c) ⧸ (PiNS W T π' 1).comap (InvS W T π' Eπ h' 1 c).subtype

abbrev LcQ (π' : LetA O n) (c : ZMod n) : Type :=
  ↥(NcS W T (c - 1)) ⧸ (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype

def JCl (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Set (G → T.V) :=
  {κ | ∃ hκ : κ ∈ latticeCocycles T.L, ∃ w ∈ InvS W T π' Eπ h' M c, ∃ z ∈ PiNS W T π' M,
    ∃ hwz : (w, z) ∈ W.wachCocyclesDelta T,
      Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) = W.clK T ⟨(w, z), hwz⟩}

def JZ (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Submodule O (G → T.V) :=
  Submodule.span O (JCl W T π' Eπ h' M c)

end Local

section Record

variable {l : ℕ} [Fact l.Prime]

abbrev eK (K : FinExt l) : ℕ := finrank ↥(K0 K) ↥K.1

abbrev sK (l : ℕ) [Fact l.Prime] (K : FinExt l) : ℕ := (l - 1) / eK K

abbrev MK (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' : ℕ) : ℕ := ⌈(4 * h' : ℝ) / (sK l K : ℝ)⌉₊

abbrev y2K (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' S η : ℕ) : ℕ :=
  2 * sigA l (sK l K) h' + kapA l (eK K) h' S + rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)

def HypN (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, JumpsInV (P.PD K) T₂.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧ (∀ τ, b τ + S ≤ h') ∧ 1 ≤ h' ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

end Record

end Formalism.MainNotions.N.Ln34

end
end

