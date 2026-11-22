import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0734
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.LubinTateReciprocity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotInDetectByEqvMap
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isotIn_detect_by_eqv_map : ∀ (D : D7) {n : ℕ} (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (y : A), y ∈ principalLevelFrame.isotIn ρ C π → y ≠ 0 → ∃ q : A →ₗ[ℂ] (GAf D.host.E n → ℂ), q y ≠ 0 ∧ ∀ z ∈ principalLevelFrame.isotIn ρ C π, q z ∈ π.S ∧ ∀ h, q (ρ h z) = NG.rt D.host.E n h (q z) := by
  intro D n A _ _ ρ C π y hy hy0
  let St : Submodule ℂ A → Prop := fun K => ∀ h, ∀ x ∈ K, ρ h x ∈ K
  have rangeSt : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → St (LinearMap.range Φ) := by
    rintro Φ hΦ h _ ⟨f, rfl⟩
    exact ⟨_, hΦ h f⟩
  have rangeLe : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → LinearMap.range Φ ≤ C →
      LinearMap.range Φ ≤ principalLevelFrame.isotIn (D := D) ρ C π := fun Φ hΦ hC =>
    le_iSup₂ (f := fun (Ψ : π.S →ₗ[ℂ] A) (_ : principalLevelFrame.IsEqvA ρ π Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ) Φ ⟨hΦ, hC⟩
  have supSt : ∀ K1 K2 : Submodule ℂ A, St K1 → St K2 → St (K1 ⊔ K2) := by
    intro K1 K2 h1 h2 h x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]; exact Submodule.add_mem_sup (h1 h a ha) (h2 h b hb)
  have atom : ∀ K : Submodule ℂ A, St K → ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ →
      LinearMap.range Φ ≤ K ∨ ∀ f, Φ f ∈ K → f = 0 := by
    intro K hK Φ hΦ
    rcases π.irr ((K.comap Φ).map π.S.subtype) (by
        rintro _ ⟨f, -, rfl⟩; exact f.2)
      (by
        rintro h _ ⟨f, hf, rfl⟩
        refine ⟨⟨NG.rt D.host.E n h f, π.stable h f f.2⟩, ?_, rfl⟩
        show Φ _ ∈ K
        rw [hΦ h f]; exact hK h _ hf) with h0 | h1
    · right; intro f hf
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := ⟨f, hf, rfl⟩
      rw [h0] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · left; rintro _ ⟨f, rfl⟩
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := by rw [h1]; exact f.2
      obtain ⟨f', hf', he⟩ := this
      have : f' = f := Subtype.ext he
      subst this; exact hf'
  obtain ⟨K, hKmax⟩ := zorn_le₀ {K : Submodule ℂ A | K ≤ principalLevelFrame.isotIn (D := D) ρ C π ∧ St K ∧ y ∉ K} (by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨bot_le, fun h x hx => ?_, fun h => hy0 ((Submodule.mem_bot ℂ).1 h)⟩, by simp⟩
      rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact zero_mem _
    · refine ⟨sSup c, ⟨sSup_le fun K hK => (hc hK).1, ?_, ?_⟩, fun K hK => le_sSup hK⟩
      · intro h x hx
        have : sSup c ≤ (sSup c).comap (ρ h) := sSup_le fun K hK z hz => le_sSup hK ((hc hK).2.1 h z hz)
        exact this hx
      · intro hyc
        obtain ⟨K, hK, hyK⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hyc
        exact (hc hK).2.2 hyK)
  obtain ⟨⟨hKN, hKSt, hyK⟩, hKm⟩ := hKmax
  have grow : ∀ K' : Submodule ℂ A, K' ≤ principalLevelFrame.isotIn (D := D) ρ C π → St K' → K ≤ K' → ¬ K' ≤ K → y ∈ K' :=
    fun K' h1 h2 h3 h4 => by
      by_contra hyK'; exact h4 (hKm ⟨h1, h2, hyK'⟩ h3)
  obtain ⟨Φ, ⟨hΦ, hΦC⟩, hΦK⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (principalLevelFrame.IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧
      ¬ LinearMap.range Φ ≤ K := by
    by_contra hcon
    push_neg at hcon
    exact hyK ((iSup₂_le fun Φ hΦ => hcon Φ hΦ : principalLevelFrame.isotIn (D := D) ρ C π ≤ K) hy)
  have hΦK' : ∀ f, Φ f ∈ K → f = 0 := (atom K hKSt Φ hΦ).resolve_left hΦK
  have hyK2 : y ∈ K ⊔ LinearMap.range Φ := grow _ (sup_le hKN (rangeLe Φ hΦ hΦC))
    (supSt _ _ hKSt (rangeSt Φ hΦ)) le_sup_left (fun h => hΦK (le_sup_right.trans h))
  have hN2 : principalLevelFrame.isotIn (D := D) ρ C π ≤ K ⊔ LinearMap.range Φ := by
    refine iSup₂_le fun Φ' hΦ' => ?_
    by_contra hnot
    have h3 := (atom _ (supSt _ _ hKSt (rangeSt Φ hΦ)) Φ' hΦ'.1).resolve_left hnot
    have hyK3 : y ∈ K ⊔ LinearMap.range Φ' := grow _ (sup_le hKN (rangeLe Φ' hΦ'.1 hΦ'.2))
      (supSt _ _ hKSt (rangeSt Φ' hΦ'.1)) le_sup_left
      (fun h => hnot ((le_sup_right.trans h).trans le_sup_left))
    obtain ⟨k, hk, _, ⟨f', rfl⟩, hsum⟩ := Submodule.mem_sup.1 hyK3
    have hf' : f' = 0 := h3 f' (by
      have : Φ' f' = y - k := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ hyK2 (Submodule.mem_sup_left hk))
    apply hyK; rw [← hsum, hf', map_zero, add_zero]; exact hk
  let Ψ : (K × π.S) →ₗ[ℂ] A := K.subtype.coprod Φ
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨k, f⟩ h0
    simp only [Ψ, LinearMap.coprod_apply, Submodule.subtype_apply] at h0
    have hneg : Φ f = -(k : A) := eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h0)
    have hf : f = 0 := hΦK' f (by rw [hneg]; exact K.neg_mem k.2)
    subst hf
    rw [map_zero, add_zero] at h0
    have hk : k = 0 := Subtype.ext h0
    subst hk; rfl
  let E := LinearEquiv.ofInjective Ψ hΨ
  let q0 : LinearMap.range Ψ →ₗ[ℂ] π.S := (LinearMap.snd ℂ K π.S).comp E.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend q0
  have hq0 : ∀ (k : K) (f : π.S), g (k + Φ f) = f := by
    intro k f
    have hmem : (k : A) + Φ f ∈ LinearMap.range Ψ := ⟨(k, f), rfl⟩
    have h1 := LinearMap.congr_fun hg ⟨_, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    have h2 : (⟨_, hmem⟩ : LinearMap.range Ψ) = E (k, f) := Subtype.ext (by simp only [E, LinearEquiv.ofInjective_apply]; rfl)
    show (E.symm _).2 = f
    rw [h2, LinearEquiv.symm_apply_apply]
  have dec : ∀ z ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∃ (k : K) (f : π.S), z = k + Φ f := by
    intro z hz
    obtain ⟨a, ha, _, ⟨f, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hN2 hz)
    exact ⟨⟨a, ha⟩, f, rfl⟩
  refine ⟨π.S.subtype ∘ₗ g, ?_, ?_⟩
  · obtain ⟨k, f, rfl⟩ := dec y hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hq0]
    intro hf
    have : f = 0 := Subtype.ext hf
    subst this
    apply hyK; rw [map_zero, add_zero]; exact k.2
  · intro z hz
    obtain ⟨k, f, rfl⟩ := dec z hz
    refine ⟨by simp [hq0], fun h => ?_⟩
    have : ρ h ((k : A) + Φ f) = ((⟨ρ h k, hKSt h k k.2⟩ : K) : A) + Φ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩ := by
      rw [map_add, hΦ h f]
    have e1 := hq0 ⟨ρ h k, hKSt h k k.2⟩ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩
    have e2 := hq0 k f
    rw [this, LinearMap.comp_apply, LinearMap.comp_apply, e1, e2]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_averages_theta_pair_zero_without_character : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  first | exact @GlobalTheory.DownLift.GenFinite.avgLaw | exact GlobalTheory.DownLift.GenFinite.avgLaw | (intros; apply GlobalTheory.DownLift.GenFinite.avgLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaine
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTClosing

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_of_le {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  intro hBS hFB C hC D HW F _ l _ K' h hN hF hS LL
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  obtain ⟨a, ha⟩ : ∃ a, a = (l - 1).factorial := ⟨_, rfl⟩
  haveI : NeZero a := ⟨by rw [ha]; exact Nat.factorial_ne_zero _⟩
  have hla : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (by omega)
  obtain ⟨e, he⟩ : ∃ e, e + 1 = l ^ a := ⟨l ^ a - 1, by omega⟩
  haveI : NeZero e := ⟨by
    intro h0
    rw [h0, zero_add] at he
    omega⟩
  have hnd : ¬ l ∣ a := by
    rw [ha, hlp.dvd_factorial]
    omega
  obtain ⟨⟨LL', hle, hUnr⟩, -⟩ := GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL
  haveI := hUnr
  haveI : TameDescentExponentData ↥LL'.1 l e a := (GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL').2 hUnr
  refine GlobalTheory.T.theoremT_descend_smaller_coefficients l (D.loc l) K' h hN hF hS LL LL' hle C ?_
  have ϖ : PiSys l e := Classical.arbitrary _
  have hStd : IsStd (D.loc l) (D.locA l) := IsStd.of_tied (D.locT l)
  intro T₁ T₂ g N η H U Sig Fr hP1 hP2 hOnto hFr hFS h1 hcard h2N hIT1 hIT2 hUr hU0 hUc hη hηH hJ1 hJ2 hl
  have hp : (pc (D.loc l) h hN hF hS).PD.p = l := (D.loc l).PD_p _
  have hlarge : 40 * (H * N ^ 2 + N ^ 3) < l := lt_of_le_of_lt (Nat.mul_le_mul_right _ hC) hl
  have hNl : N < l := by
    have : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
    omega
  have hcop : ∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l := fun χ hχ => by
    have := hIT1.2.1 χ hχ
    rwa [hp] at this
  obtain ⟨Sig', hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd ha
    K' h hN hF hS Sig Fr N hFr hFS h1 hcard hNl hIT1.1 hcop
  obtain ⟨c1, t1⟩ := hS5 T₁ hP1 hIT1
  obtain ⟨c2, t2⟩ := hS5 T₂ hP2 hIT2
  have hnum : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig' U :=
    ⟨hS1, hS2, hS3, h2N, hUr, hU0, hUc, hη, hηH, hlarge⟩
  have hcore := GlobalTheory.T.lift_surjection_good_crystalline_lattices hBS hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd N η H Sig' U hnum T₁ T₂ g hOnto
    ⟨c1, t1, hJ1⟩ ⟨c2, t2, hJ2⟩
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hlp (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) he Sig' N hS1 hS2 hS3 h2N
  rw [hS4] at hcore horb
  refine ⟨horb.2.1, ?_⟩
  exact liftF_of_le _ g hcore (Nat.mul_le_mul_right _ (by omega))

end GlobalTheory.TheoremTClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem LocLanglands.isSmoothChar_of_comp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (hs : Function.Surjective a)
    (hc : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ))
    (ho : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : WeilDeligne.IsSmooth (χ.comp a)) : IsSmoothChar χ := by
  haveI : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have hK : IsOpen {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1} := hχ
  have hC : IsClosed ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ) :=
    (hK.isClosed_compl.isCompact.image hc).isClosed
  have hU : {x : (w.adicCompletion E)ˣ | valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1} ∈ nhds 1 := by
    have h1 : {x : w.adicCompletion E | valuation (w.adicCompletion E) (x - 1) < 1} ∈ nhds 1 := by
      rw [IsValuativeTopology.mem_nhds_iff]
      exact ⟨1, fun z hz => by simpa [neg_add_eq_sub] using hz⟩
    have h2 := Units.continuous_val.continuousAt (x := (1 : (w.adicCompletion E)ˣ)) h1
    refine Filter.mem_of_superset h2 fun x hx => ?_
    have h3 : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - 1) < 1 := hx
    have := Valuation.map_one_add_of_lt _ h3
    simpa using this
  refine Subgroup.isOpen_of_mem_nhds χ.ker (g := 1) ?_
  have h1 : (1 : (w.adicCompletion E)ˣ) ∈ ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ)ᶜ := by
    rintro ⟨σ, hσ, e⟩
    refine hσ ?_
    have e' : a (ineIncl h σ) = 1 := e
    simp [e']
  refine Filter.mem_of_superset (Filter.inter_mem hU (hC.isOpen_compl.mem_nhds h1)) ?_
  rintro x ⟨hx, hx'⟩
  obtain ⟨σ, rfl⟩ := hs x
  have h0 : deg σ = 0 := by
    have := ho σ
    rw [ord_eq_zero_iff.2 hx] at this
    omega
  by_contra hn
  exact hx' ⟨⟨σ, deg_eq_zero_iff.mp h0⟩, hn, rfl⟩

theorem localArtinExists_holds : LocalArtinExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨art, hart⟩ := globalArtinReciprocity_holds E Ω
  obtain ⟨a, hs, ho, hg⟩ := T.exists_inverse_localArtin_weilGroup_hom E Ω A w h art hart
  have hc := T.inverseLocalArtin_continuousOn_inertia E Ω A w h art a hart ho hg
  refine ⟨a, hs, hc, ho, fun ξ hξ => ?_, fun art' hart' => ?_⟩
  · have hker : a.ker ≤ ξ.ker := fun σ hσ => by
      refine T.smoothWeilChar_eq_one_of_toAbsGaloisAb_eq_one E Ω A w h ξ hξ σ ?_
      rw [← hg σ, MonoidHom.mem_ker.1 hσ, map_one, map_one]
    have e : ξ = (a.liftOfSurjective hs ⟨ξ, hker⟩).comp a :=
      (MonoidHom.liftOfRightInverse_comp a _ (Function.rightInverse_surjInv hs) ⟨ξ, hker⟩).symm
    exact ⟨_, isSmoothChar_of_comp hs hc ho (e ▸ hξ), e⟩
  · rw [T.globalArtinReciprocityMap_unique E Ω art' art hart' hart]
    exact hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusActionStatement
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_artin_frobenius_action : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ (σ : Weil h) (τ : GalLoc w), Lifts ι τ (σ : G E Ω) →
    ∀ (z : Kbar w) (hz : z ∈ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      τ ((localArtinMap (w.adicCompletion E) (Kbar w) (a σ) ⟨z, hz⟩ : maximalAbelianExtension (w.adicCompletion E) (Kbar w)) : Kbar w) = z := by
  first | exact @GlobalTheory.ArtinCompareApply.lift_localArtinMap_apply | exact GlobalTheory.ArtinCompareApply.lift_localArtinMap_apply | (intros; apply GlobalTheory.ArtinCompareApply.lift_localArtinMap_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory.ArtinInertia

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitAt_artin_ine : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  intro E' Ω _ _ _ _ _ A w' h' a' ha t
  have h1 := ha.ord_eq (ineIncl h' t)
  rw [deg_ineIncl, neg_zero, SphCompletion.ord_completion, neg_eq_zero] at h1
  have h0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by simp
  show Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

end GlobalTheory.ArtinInertia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isLocalArtin_transport : GlobalArtinReciprocity → ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (a' : Weil h' →* (w'.adicCompletion E')ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ σ σ', WeilRel φ σ σ' → a' σ' = Units.map i.toRingHom.toMonoidHom (a σ) := by
  intro hG hC E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP a a' ha ha' σ σ' hσ
  obtain ⟨art, hart⟩ := hG E Ω
  obtain ⟨art', hart'⟩ := hG E' Ω'
  let x : (w.adicCompletion E)ˣ := Units.map i.symm.toRingHom.toMonoidHom (a' σ')
  have hx : Units.map i.toRingHom.toMonoidHom x = a' σ' := by
    ext
    simp [x]
  have h1 := GlobalTheory.T.globalArtin_compat_localDegreeOne E Ω A w h E' Ω' A' w' h' φ j i hP art art' hart hart' σ σ' x hσ
    (by rw [hx]; exact ha'.glob art' hart' σ')
  have h2 : x = a σ := GlobalTheory.T.globalArtin_localIdele_injective hC E Ω art hart w (h1.trans (ha.glob art hart σ).symm)
  rw [← hx, h2]

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocalSum

open GlobalTheory.PRep

theorem exists_eigen_family {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ u : ι → V, (∀ j, ∀ h ∈ K, ρ h (u j) = θ h • u j) ∧ ∑ i, T i (u i) = ∑ i, T i (y i) := by
  first
  | exact @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | (apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family ..)

set_option maxHeartbeats 1000000 in

theorem exists_eigen_local_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ U hK hKOne hU hU1 hθU f hf hθ ι _ xs z hxs hz
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hz
    simp
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := GlobalTheory.EigLocal.exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono hKOne GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  have hint : ∀ (j : F.support) (x : GAf L n), TrivOutside {s.v} x → ∀ v,
      (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
        (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) v) := fun j x hx v => j.1.2.2 x hx v
  obtain ⟨u, hu, hus⟩ := exists_eigen_family σ.smooth hKc hU hU1 θ hθU hmul
    (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))) (fun j => y j.1) (by
      intro k hk
      obtain ⟨x, hx, e, hfx⟩ := hrt k hk
      subst e
      rw [Finset.sum_congr rfl fun j _ => hint j x hx (y j.1), ← map_sum, hsum, hfx])
  rw [hsum] at hus
  by_contra hall
  push_neg at hall
  apply hz
  have key : ∀ j, ∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j) = 0 := by
    intro j
    by_contra hne
    exact hne (hall (u j) (hu j))
  calc ∑ m, z m • NG.rt L n (xs m) f
      = ∑ m, z m • ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← hus, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (hint j (xs m) (hxs m) (u j)).symm
    _ = ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        simp only [map_sum, map_smul, Finset.smul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [key j, map_zero]

end GlobalTheory.EigLocalSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_typePlaceCompletionIdent : ∀ D : D7, Nonempty (Ident D) := by
  first | exact @GlobalTheory.TypeIdent.nonempty_ident | exact GlobalTheory.TypeIdent.nonempty_ident | (intros; apply GlobalTheory.TypeIdent.nonempty_ident <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionGLSurjective
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.GLp.reduction_GL_surjective : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), Function.Surjective (GlobalTheory.GLp.red g n) :=
  fun g _ n => GlobalTheory.GLp.red_surjective g n
end

