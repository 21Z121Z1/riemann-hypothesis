import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0506
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecompStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_induction_character_restriction_decomp : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∀ (α : Gn g a → ℂ) (β : Gn g b → ℂ), IsChar α → IsChar β → IsChar (hc a b α β n)) ∧ ∀ χ : Gn g n → ℂ, IsChar χ → ∃ L : List ((Gn g a → ℂ) × (Gn g b → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, res a b χ x y = (L.map fun p => p.1 x * p.2 y).sum := by
  first | exact @GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp | exact GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp | (intros; apply GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HatOfInvariantSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.TwoMaps

theorem toHatS_eq_of_hat : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → toHatS O K l e f = x := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f x hfx
  let fR : Rpi O K l e := ⟨(f : K⟦X⟧), invL_S_le_Rpi l e f.2⟩
  have h0 : hat O l e (fR : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHat O K l e fR) := hat_coe_Rpi l e fR
  have h1 : toHatS O K l e f = toHat O K l e fR := rfl
  have h2 : hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHatS O K l e f) := by
    rw [h1]; exact h0
  rw [h2] at hfx
  have hE0 : EIn l e (invL l (A O K)) ≠ 0 := fun h => by
    have h3 : E K l e = 0 := congrArg Subtype.val h
    exact (isUnit_E (K := K) l e).ne_zero h3
  have hreg : ∀ y : Ahat O K l e, Ehat O K l e * y = 0 → y = 0 := fun y hy =>
    GlobalTheory.MemLoc.FilPrincipal.regular_of_isDomain rfl hE0 y hy
  have hmem : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro y hy <;> apply hreg <;> first | exact hy | (rw [mul_comm]; exact hy)
  have hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
    IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) (AhatE O K l e) (Submonoid.powers_le.2 hmem)
  exact hinj hfx

theorem iSD_eq_of_mem_invL_A : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)), (f : K⟦X⟧) ∈ invL l (A O K) → ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f hf
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]

theorem iSD_eq_iHat_of_hat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K], ∀ (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → ϖ.iSD O K f = ϖ.iHat O K x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ f x hfx
  obtain rfl := toHatS_eq_of_hat l e O K ϖ f x hfx
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ

  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) = crisToOD l O (ϖ.iS O K s) :=
    fun s => ϖ.iSD_of_mem O K s.2 _
  have key : ∀ s : S O K e, crisToOD l O (ϖ.iS O K s) =
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
    intro s
    rw [← sub_eq_zero]
    set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
    have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
      simp only [hD, map_add]; ring
    have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
      simp only [hD, map_mul, map_pow, map_natCast]; ring
    have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
      intro m
      obtain ⟨N, hN⟩ := GlobalTheory.T.exists_pow_mul_crisToOD_sub_toOD_dvd l e O K ϖ m
      have hw : ∀ k : ℕ, ∃ y : OA l O, ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
        intro k
        obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
        obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
        set hS' : S O K e := ⟨h, hh⟩
        have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
          sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
        set P : S O K e := ⟨_, hP⟩
        have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
        have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
          have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
            simp only [P]; linear_combination hs
          rw [this]
          exact sum_mem fun n _ => monomial_mem_invL l n _
        have hDP : D P = 0 := by
          simp only [hD, sub_eq_zero]
          rw [← hS]
          exact iSD_eq_of_mem_invL_A l e O K ϖ _ hPA
        obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
        obtain ⟨y2, hy2⟩ := GlobalTheory.T.exists_pow_iHat_toHatS_sub_toOD_dvd l e O K ϖ m hS'
        refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
        have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
            (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') - toOD l O y1) -
              (l : OD l O) ^ N * ((l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
          rw [hsP, hDadd, hDP, zero_add, hDmul]
          simp only [hD, map_sub, map_mul, map_pow, map_natCast]
          ring
        rw [e1]
        exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
      have h1 := GlobalTheory.T.dvd_of_forall_approx_toOD l e O K ϖ m _ hw
      rw [pow_add, mul_assoc] at h1
      exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
    have hc := ϖ.complete_OD O K
    exact hc.toIsHausdorff.haus' _ fun n => by
      simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
      exact Ideal.mem_span_singleton.2 (hdiv n)
  have hext : ϖ.iSD O K = (ϖ.iHat O K).toRingHom.comp (toHatS O K l e) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) (RingHom.ext fun s => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact (hS s).trans (key s))
  exact RingHom.congr_fun hext f

end GlobalTheory.BKReal.TwoMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegralityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  first | exact @GlobalTheory.LatTied.latStable_tied | exact GlobalTheory.LatTied.latStable_tied | (intros; apply GlobalTheory.LatTied.latStable_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValues
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.HerrClassUniq

theorem cocycle_eq {l : ℕ} [Fact l.Prime] {G V LL : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [T2Space LL]
    [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (a : G → V → V) (c c' : G → V) (hc : Continuous c) (hc' : Continuous c')
    (ha : ∀ x, a 1 x = x)
    (hcc : ∀ g h, c (g * h) = c g + a g (c h)) (hcc' : ∀ g h, c' (g * h) = c' g + a g (c' h))
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1) (hker : ∀ h, lam h = 1 → c h = c' h) (hg₀ : c g₀ = c' g₀) :
    c = c' := by
  have h1 : c 1 = 0 := by
    have := hcc 1 1
    simpa [ha] using this
  have h1' : c' 1 = 0 := by
    have := hcc' 1 1
    simpa [ha] using this
  let S : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := fun {a b} ha hb => by
        change c (a * b) = c' (a * b)
        rw [hcc, hcc', show c a = c' a from ha, show c b = c' b from hb]
      one_mem' := by
        change c 1 = c' 1
        rw [h1, h1']
      inv_mem' := fun {a} ha => by
        change c a⁻¹ = c' a⁻¹
        have e1 := hcc a⁻¹ a
        have e2 := hcc' a⁻¹ a
        rw [inv_mul_cancel, h1, show c a = c' a from ha] at e1
        rw [inv_mul_cancel, h1'] at e2
        exact add_right_cancel (e1.symm.trans e2) }
  have hS : IsClosed (S : Set G) := by
    have : {g | c g = c' g} = ⋂ f : Module.Dual LL V, {g | f (c g) = f (c' g)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h f => by rw [h], fun h => ?_⟩
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff LL]
      intro f
      rw [map_sub, h f, sub_self]
    change IsClosed {g | c g = c' g}
    rw [this]
    refine isClosed_iInter fun f => ?_
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    exact isClosed_eq (hf.comp hc) (hf.comp hc')
  funext g
  have hcl : IsClosed (lam '' (S : Set G)) := (hS.isCompact.image hlam).isClosed
  have hsub : Set.range (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) ⊆ lam '' (S : Set G) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨g₀ ^ n, S.zpow_mem (show g₀ ∈ S from hg₀) n, ?_⟩
    rw [map_zpow, h₀, ← ofAdd_zsmul]
    simp
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) :=
    PadicInt.denseRange_intCast
  have hmem : lam g ∈ lam '' (S : Set G) := hcl.closure_subset_iff.2 hsub (hd (lam g))
  obtain ⟨x, hx, hxg⟩ := hmem
  have h2 : g * x⁻¹ ∈ S := hker _ (by rw [map_mul, map_inv, hxg, mul_inv_cancel])
  have h3 : g ∈ S := by simpa using S.mul_mem h2 hx
  exact h3

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem val_eq_of_Zf {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K))
    (c c' : ↥(latticeCocycles (resLat T H))) (b : TW (RW LL) T) (g : ↥H) (e : Zf AI T H c b g = Zf AI T H c' b g) :
    (c : ↥H → T.V) g = (c' : ↥H → T.V) g := by
  unfold Zf at e
  exact congrArg Subtype.val ((GlobalTheory.WittTensorFixed.main l K LL T).2.2 (add_right_cancel e))

set_option maxHeartbeats 1000000 in

theorem cocycle_eq_lat {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K)) (hH : IsClosed (H : Set ↥(GK K)))
    (c c' : ↥(latticeCocycles (resLat T H)))
    (lam : ↥H →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : ↥H)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (hker : ∀ h, lam h = 1 → (c : ↥H → T.V) h = (c' : ↥H → T.V) h)
    (hg₀ : (c : ↥H → T.V) g₀ = (c' : ↥H → T.V) g₀) : c = c' := by
  haveI := GlobalTheory.HerrClassMaps.compact_GK K
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.1 hH.isCompact
  haveI := T.mtop
  exact Subtype.ext (cocycle_eq (LL := ↥LL.1) (V := T.V) (fun (g : ↥H) (x : T.V) => T.ρ (g : ↥(GK K)) x) c c' c.2.1.1 c'.2.1.1
    (fun x => by simp) c.2.1.2 c'.2.1.2 lam hlam g₀ h₀ hker hg₀)

set_option maxHeartbeats 2000000 in

theorem class_of_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  intro D HW F l _ K s LL h T c b y z hyz g₀ hg₀ hb hk hz
  refine (cl_fit D HW F K s LL h T y z hyz b hb).elim fun cW hW => ?_
  refine (lam_exists D HW K s LL h).elim fun lam hl => ?_
  have e : c = cW := cocycle_eq_lat T _ hl.2.2.2.2 c cW lam hl.1 g₀ ((hl.2.2.1 g₀).2 hg₀)
    (fun g hg => val_eq_of_Zf (D.locA l) T _ c cW b g
      ((hk g ((hl.2.1 g).1 hg)).trans (hW.2.1 g ((hl.2.1 g).1 hg)).symm))
    (val_eq_of_Zf (D.locA l) T _ c cW b g₀ (hz.trans (hW.2.2 g₀ hg₀).symm))
  exact (congrArg Submodule.Quotient.mk e).trans hW.1

end GlobalTheory.NL.HerrClassUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelations
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.HerrCocycleCriterion

theorem herr_of_tie {O D M : Type} [CommRing O] [AddCommGroup D] [Module O D] [AddCommGroup M]
    [Module O M] (γ φ : D →ₗ[O] D) (g Φ : M →ₗ[O] M) (j : D →ₗ[O] M) (hj : Function.Injective j)
    (y z : D) (b t : M) (hγ : j (γ y) = g (j y)) (hφ : j (φ z) = Φ (j z))
    (hc : Φ (g b) = g (Φ b)) (ht : Φ t = t) (hy : Φ b - b = j y) (hz : t + (g b - b) = j z) :
    (y, z) ∈ herrCocycles γ φ := by
  simp only [herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply]
  apply hj
  rw [map_zero, map_add, map_neg, map_sub, map_sub, hγ, hφ, ← hy, ← hz, map_add, map_sub, map_sub,
    hc, ht]
  abel

theorem TWmap_one {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R]
    [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWmap f T ((1 : R) ⊗ₜ[O] t) = (1 : R) ⊗ₜ[O] t := by
  simp [TWmap]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cocyc : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  intro D HW F l _ K s LL h T c b y z g₀ hg hy hz
  have h1 := ((F l).E K s LL h).tie.jD_act T (g₀ : ↥(GK K)) y
  rw [hg] at h1
  exact herr_of_tie _ _ _ _ _ (((F l).E K s LL h).tie.jD_inj T) y z b _ h1
    (((F l).E K s LL h).tie.jD_φ T z)
    (GlobalTheory.HerrClassMaps.TWmap_act _ _ (GlobalTheory.HerrClassMaps.phi_gRW (D.locA l) LL _) T _ b)
    (TWmap_one _ T _) hy hz

end GlobalTheory.NL.HerrCocycleCriterion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamily
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  intro l _ P AI T C hFit ξ hξ K K' a ρ w k hw hspan hinv
  classical
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l

  have hE : IsUnit (ι (aDp l ξ)) := by
    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have h1 := GlobalTheory.MemLoc.TiedUnif.isUnit_xi (core_isEps l C)
    rw [← hc0, map_mul, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1

  set q : ℕ := ∑ i, (k i).natAbs with hq
  have hkq : ∀ i, 0 ≤ k i + q := by
    intro i
    have h1 : (k i).natAbs ≤ q := Finset.single_le_sum (f := fun i => (k i).natAbs) (by simp) (Finset.mem_univ i)
    omega
  set p : Fin a → ℕ := fun i => (k i + q).toNat with hp
  have hkp : ∀ i, k i + q = (p i : ℤ) := fun i => (Int.toNat_of_nonneg (hkq i)).symm

  have hV0 : ∀ i j, ∃ v : Per.BdRp l, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * v) :=
    fun i j => exists_xi_pow_mul l P AI T C ξ hξ K (k j) q (p j) (hkp j) (w j i) (hw j i)
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin a) (Fin a) (Per.BdRp l), ∀ i j, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * V i j) :=
    ⟨fun i j => Classical.choose (hV0 i j), fun i j => Classical.choose_spec (hV0 i j)⟩

  choose u hu hsum using hspan
  have hz0 : ∀ j i, ∃ z : Per.BdRp l, ι (aDp l ξ) ^ p i * T.eD (u j i) = ι (aDp l ξ ^ q * z) :=
    fun j i => exists_xi_pow_mul l P AI T C ξ hξ K (-k i) (p i) q (by have := hkp i; omega) (u j i) (hu j i)
  choose z hz using hz0
  have key : ∀ j j', ∑ i, z j i * V j' i = if j' = j then 1 else 0 := by
    intro j j'
    apply hinj
    have hs := congrFun (hsum j) j'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    have h1 : ι (aDp l ξ) ^ q * ι (∑ i, z j i * V j' i) =
        ι (aDp l ξ) ^ q * T.eD (∑ i, u j i * w i j') := by
      rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ha := hV j' i
      have hb := hz j i
      simp only [map_mul, map_pow] at ha hb ⊢
      calc ι (aDp l ξ) ^ q * (ι (z j i) * ι (V j' i))
          = (ι (aDp l ξ) ^ q * ι (z j i)) * ι (V j' i) := by ring
        _ = (ι (aDp l ξ) ^ p i * T.eD (u j i)) * ι (V j' i) := by rw [hb]
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ p i * ι (V j' i)) := by ring
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ q * T.eD (w i j')) := by rw [ha]
        _ = ι (aDp l ξ) ^ q * (T.eD (u j i) * T.eD (w i j')) := by ring
    rw [(hE.pow q).mul_left_cancel h1, hs, Pi.single_apply]
    split_ifs <;> simp
  set N : Matrix (Fin a) (Fin a) (Per.BdRp l) := Matrix.of fun i j => z j i with hN
  have hVN : V * N = 1 := by
    ext j' j
    rw [Matrix.mul_apply, Matrix.one_apply, ← key j j']
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hN, Matrix.of_apply]; ring
  have hNV : N * V = 1 := mul_eq_one_comm.1 hVN
  refine ⟨⟨V, ⟨⟨V, N, hVN, hNV⟩, rfl⟩, p, q, Matrix.of fun i j => T.eD (w j i), fun i j => by simpa using hV i j, ?_⟩, ?_⟩
  · intro g hg
    ext r c
    have h := congrArg T.eD (congrFun (hinv g hg c) r)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, T.actD, hFit.o] at h
    rw [Matrix.mul_apply]
    simpa [Matrix.map_apply, Matrix.of_apply, GlobalTheory.MemLoc.Core.oD] using h
  · intro n
    have hf : (Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n) = Finset.univ.filter fun i => k i = n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hkp i
      omega
    show ((Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n).card : ℤ) = _
    rw [hf, Finset.card_filter]
    push_cast
    rfl

end GlobalTheory.HodgeAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExtStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeJumpMultiplicity_restrict_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  first | exact @GlobalTheory.JumpRestrict.multV_restrict | exact GlobalTheory.JumpRestrict.multV_restrict | (intros; apply GlobalTheory.JumpRestrict.multV_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtensionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  first | exact @GlobalTheory.BaseCoef.jumpsInV_extLat | exact GlobalTheory.BaseCoef.jumpsInV_extLat | (intros; apply GlobalTheory.BaseCoef.jumpsInV_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariantStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.colHT_equivariant) | (exact GlobalTheory.HTBasis.colHT_equivariant) | (intros; apply GlobalTheory.HTBasis.colHT_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixIsUnitDetStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) → ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) → LinearIndependent P.R.BdR u → IsUnit (colHT J u k).det := by
  first | (exact @GlobalTheory.HTBasis.colHT_isUnit_det) | (exact GlobalTheory.HTBasis.colHT_isUnit_det) | (intros; apply GlobalTheory.HTBasis.colHT_isUnit_det  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HsumMulEisensteinCompletionPowIntegralStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  first | exact @GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow | exact GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow | (intros; apply GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HubXTypePrimeConditions
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem hubX_typePrime_conditions : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → AdmissibleParameterJ.JumpConditions L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → SumRepresentations.ConclusionG5 D → GlobalTheory.HubX.LgcG D → GlobalTheory.HubX.DepthZeroG D → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U ∧ PairedCharacterCondition.SetSQ i (X.r i)) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  intro D L HW R X hX P hJ hadm hG5 hLgc hDZ CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hadm' : L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := hadm
  have hb : 1 ≤ L.sc.b := by linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.b := by linarith
  obtain ⟨hnum1, hnum2, hnum3⟩ := GlobalTheory.typePrime_exceeds_constant D L P (by linarith) hb CT hCT
  obtain ⟨hJa, hJb, hJc, -, hJe, -, -⟩ := hJ
  have hJaAt : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D (GlobalTheory.HubX.epJ D) := by
    rw [GlobalTheory.HubX.epJ_eq hJa]; exact hJa.choose_spec
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hX.fam.good
  have hpt := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hX.fam
  rw [hX.eta]
  refine ⟨fun i k _ hk hHG => ⟨hgood i, fun π hπ => ⟨(hpt i π hπ).1, (hpt i π hπ).2.1⟩, ?_⟩, hnum2⟩
  obtain ⟨sg, U, hsg, hU⟩ := GlobalTheory.T.signs_and_jump_sets_at_type_prime D L (GlobalTheory.HubX.epJ D) hJaAt hJb hJc hJe ht i k (X.r i) hk (hgood i)
  obtain ⟨hJ09, hadm5⟩ := GlobalTheory.T.tame_descent_conditions_every_localisation D i
  have hSQ := GlobalTheory.T.local_global_compatibility_at_types D i (X.r i) hG5 hHG (hgood i) hadm5 hJ09
    (fun w hw hwg => ⟨hLgc i (X.r i) (hgood i) w hw hwg, hDZ i w hw hwg⟩)
  refine ⟨⌊3 * L.sc.b⌋₊ + 2, 0, sg, U, hnum1, hnum3 k, hsg, hU, hSQ⟩

end GlobalTheory
end

