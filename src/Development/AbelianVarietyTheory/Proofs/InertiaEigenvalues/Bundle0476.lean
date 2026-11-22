import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixingKummerRootMovesLess
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.TameInertiaCyclic GlobalTheory.MemLoc.FrobLaws

noncomputable section
namespace GlobalTheory.NearRoot

variable {l : ℕ} [hl : Fact l.Prime]

theorem ratio_one (g : GQ l) : GlobalTheory.TameInertiaCyclic.ratio g 1 = 1 :=
  Subtype.ext (by show g 1 / 1 = 1; simp)

theorem ratio_pow (g : GQ l) (x : Om l) (n : ℕ) :
    GlobalTheory.TameInertiaCyclic.ratio g (x ^ n) = GlobalTheory.TameInertiaCyclic.ratio g x ^ n := by
  induction n with
  | zero => simpa using ratio_one g
  | succ n ih => rw [pow_succ, GlobalTheory.TameInertiaCyclic.ratio_mul, ih, pow_succ]

theorem norm_natCast_lt_one : ‖(l : Om l)‖ < 1 := by
  have h : ‖((l : ℚ_[l]) : Om l)‖ < 1 := by
    rw [PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
  simpa using h

theorem natCast_ne_zero : (l : Om l) ≠ 0 := by
  have h : ((l : ℚ_[l]) : Om l) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] (Om l)).injective]
    exact_mod_cast hl.out.ne_zero
  simpa using h

theorem exists_unif (F : FinExt l) :
    ∃ ϖ ∈ F.1, ϖ ≠ 0 ∧ (∀ x ∈ F.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖ϖ ^ k‖) ∧
      ∃ E : ℕ, 0 < E ∧ ‖ϖ‖ ^ E = ‖(l : Om l)‖ := by
  obtain ⟨π, hπ, hπ0, hgen⟩ := GlobalTheory.TameInertiaCyclic.exists_gen F
  have hlF : (l : Om l) ∈ F.1 := natCast_mem _ l
  obtain ⟨k0, hk0⟩ := hgen _ hlF natCast_ne_zero
  have hk0' : k0 ≠ 0 := by
    rintro rfl
    have := norm_natCast_lt_one (l := l)
    rw [hk0] at this
    simp at this
  rcases lt_or_gt_of_ne hk0' with hneg | hpos
  · refine ⟨π⁻¹, inv_mem hπ, inv_ne_zero hπ0, fun x hx hx0 => ?_, (-k0).toNat, by omega, ?_⟩
    · obtain ⟨k, hk⟩ := hgen x hx hx0
      exact ⟨-k, by rw [hk, _root_.inv_zpow', neg_neg]⟩
    · rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), _root_.inv_zpow', neg_neg]
  · refine ⟨π, hπ, hπ0, hgen, k0.toNat, by omega, ?_⟩
    rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

theorem near_root : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ := by
  intro l _ F
  obtain ⟨ϖ, hϖ, hϖ0, hgen, E, hE, hEn⟩ := exists_unif F
  obtain ⟨s, M, hlM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hE.ne' l (Fact.out : l.Prime).ne_one
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hlM)
  refine ⟨M, hM, hlM, fun ρ hρ g hg hgρ x hx hx0 => ?_⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne', eq_comm, neg_eq_zero] at hρ
    exact natCast_ne_zero hρ
  have hq0 : ϖ ^ (l ^ s) ≠ 0 := pow_ne_zero _ hϖ0
  have hnq : ‖ϖ ^ (l ^ s)‖ = ‖ρ‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 ?_
    rw [← norm_pow, ← pow_mul, norm_pow, hEn, ← norm_pow, hρ, norm_neg]
  set u := ϖ ^ (l ^ s) / ρ with hu
  have hu0 : u ≠ 0 := div_ne_zero hq0 hρ0
  have hnu : ‖u‖ = 1 := by rw [hu, norm_div, hnq, div_self (norm_ne_zero_iff.2 hρ0)]
  have h1 : res (GlobalTheory.TameInertiaCyclic.ratio g u) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hu0, hnu]; exact hg u hnu.le
  have h2 : res (GlobalTheory.TameInertiaCyclic.ratio g ρ) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hρ0, hgρ, sub_self, norm_zero]
    exact norm_pos_iff.2 hρ0
  have h3 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) ^ (l ^ s) = 1 := by
    rw [← map_pow, ← ratio_pow, ← div_mul_cancel₀ (ϖ ^ (l ^ s)) hρ0, ← hu,
      GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h1, h2, one_mul]
  have h4 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) = 1 := by
    have h5 : (res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) - 1) ^ (l ^ s) = 0 := by
      rw [sub_pow_char_pow, h3, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h5)
  obtain ⟨k, hk⟩ := hgen x hx hx0
  have hp : ϖ ^ k ≠ 0 := zpow_ne_zero k hϖ0
  have hv : ‖x / ϖ ^ k‖ = 1 := by rw [norm_div, hk, div_self (norm_ne_zero_iff.2 hp)]
  have h6 : res (GlobalTheory.TameInertiaCyclic.ratio g (x / ϖ ^ k)) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff _ (div_ne_zero hx0 hp), hv]
    exact hg _ hv.le
  rw [← GlobalTheory.TameInertiaCyclic.res_ratio_iff _ hx0, ← div_mul_cancel₀ x hp,
    GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h6,
    GlobalTheory.TameInertiaCyclic.res_ratio_zpow _ hϖ0 h4, one_mul]

end GlobalTheory.NearRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
section
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

structure IsAttachedAway : Prop where
  cont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))
  ss : IsSSRep r
  away : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r = T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))
  temp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.tempered (D.naut.locG π w)

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {w : PlE D.host}
  (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O)

structure IsDeRhamOf : Prop where
  deRham : IsdRAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)
  jumps : ∀ (τ : D.host.E →+* Qbar l) (L : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced Bw τ τ' →
    ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      (D.naut.infG π (ι.toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2) ∧
      IsJumpsAt (D.loc l) Bw (resDec D.nd.plOm.1 r w) τ J

structure IsAttachedAll : Prop extends IsAttachedAway D T ι π s r where
  above : ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O) (hj : Induces Bw),
    IsDeRhamOf D ι π s r Bw ∧ wdAt (D.loc l) ι Bw (D.nd.plOm.2 w) hj (resDec D.nd.plOm.1 r w) =
      T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))

structure IsAttachedHodge : Prop extends IsAttachedAway D T ι π s r where
  above : ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
    IsDeRhamOf D ι π s r Bw ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)) ∧
      (D.naut.mono0 (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w))

def GalAll : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r) (s : ℝ), D.naut.csd π → RegAlgShift D.naut π s →
    ∃ r, IsAttachedAll D T ι π s r

def GalHodge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r) (s : ℝ), D.naut.csd π → RegAlgShift D.naut π s →
    ∃ r, IsAttachedHodge D T ι π s r

def FrobMatch {K : Type} [CommRing K] (φ : K →+* ℂ) (M : G D.host.E D.nd.Om →* GL (Fin a) K) (u : ℝ) : Prop :=
  ∀ᶠ w : PlE D.host in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    (M σ : Matrix (Fin a) (Fin a) K).charpoly.map φ =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) u)).map fun α => X - C α).prod

variable {D T ι π s r}

theorem IsAttachedAll.hodge (hB : GlobalTheory.Published.DeRhamPotSemistable) (h : IsAttachedAll D T ι π s r) :
    IsAttachedHodge D T ι π s r := by
  refine ⟨h.toIsAttachedAway, fun w hw O _ _ _ Bw hj => ?_⟩
  obtain ⟨h1, h2⟩ := h.above w hw O Bw hj
  have hp := hB.isPstAt (D.locT l) Bw (resDec D.nd.plOm.1 r w) (h.cont.comp continuous_subtype_val) h1.deRham
  refine ⟨h1, fun hu => ?_, fun hm => ?_⟩
  · rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw (D.nd.plOm.2 w) hj (D.loc l) ι _ hp, h2, ← T.unr, D.naut.unr_tw]
    exact hu
  · rw [← GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw (D.nd.plOm.2 w) hj (D.loc l) ι _ hp, h2, ← T.mono0, D.naut.monomial_twist_iff]
    exact hm

theorem GalAll.hodge (hB : GlobalTheory.Published.DeRhamPotSemistable) (h : GalAll D T) : GalHodge D T :=
  fun l _ ι π s hc hr => (h l ι π s hc hr).imp fun _ H => H.hodge hB

theorem IsAttachedAway.frob (h : IsAttachedAway D T ι π s r) {w : PlE D.host}
    (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (hu : D.naut.unr (D.naut.locG π w)) :
    (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))).map fun α => X - C α).prod := by
  have h1 := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
  have h2 : (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r).unr := by rw [h.away w hl, ← T.unr]; exact h1
  refine ⟨(GlobalTheory.WeilDeligne.unr_wdOf_iff hl ι h.cont).1 h2, fun B σ hB hσ => ?_⟩
  rw [GlobalTheory.WeilDeligne.frobEig_wdOf hl ι h.cont h2 hB hσ, h.away w hl, T.frobEig w _ h1]

theorem IsAttachedAway.isGaloisRepOf (h : IsAttachedAway D T ι π 0 r) : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.IsGaloisRepOf D π l ι r := by
  refine ⟨h.cont, h.ss, fun w hw => ⟨fun σ hσ => ?_, ?_, fun hu B σ hB hσ => ?_⟩⟩
  · rw [GlobalTheory.WeilDeligne.inePol_wdOf hw ι h.cont hσ, h.away w hw, zero_add, T.inePol w _ σ hσ]
  · rw [← GlobalTheory.WeilDeligne.weilDeligneParam_monodromy_eq_zero_iff hw ι h.cont, h.away w hw, zero_add, T.mono0]
  · simpa only [zero_add, galPol] using (h.frob hw hu).2 B σ hB hσ

end GlobalTheory.TripleLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.TwistCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W] [FiniteDimensional LL W]

theorem isCrys_twist (ht : TensorCrys PD LL) (hq : QuotCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) (cρ : IsCrys PD ρ) : IsCrys PD ρ' := by
  let f : V ⊗[LL] W →ₗ[LL] V := (TensorProduct.rid LL V).toLinearMap ∘ₗ lam.lTensor V
  have hf : ∀ v x, f (v ⊗ₜ x) = lam x • v := fun v x => by simp [f]
  refine hq (V ⊗[LL] W) (ρ.tprod ν) V ρ' f ?_ ?_ (ht V ρ W ν cρ cν)
  · intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v y =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, hf, hf, hν, hρ, map_smul, map_smul,
        smul_eq_mul, mul_smul]
  · intro v
    exact ⟨v ⊗ₜ w, by rw [hf, hw, one_smul]⟩

theorem isCrys_twist_iff (ht : TensorCrys PD LL) (hq : QuotCrys PD LL) (hd : DualCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) : IsCrys PD ρ ↔ IsCrys PD ρ' := by
  refine ⟨isCrys_twist PD ht hq ρ ρ' ν χ lam w hw hν hρ cν, ?_⟩
  have hinv : ∀ g, χ g⁻¹ * χ g = 1 := fun g => by
    have h1 : ν g⁻¹ (ν g w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have h2 := congrArg lam h1
    rwa [hν, hν, map_smul, map_smul, hw, smul_eq_mul, smul_eq_mul, mul_one] at h2
  refine isCrys_twist PD ht hq ρ' ρ ν.dual (fun g => χ g⁻¹) (Module.Dual.eval LL W w) lam hw
    (fun g f => ?_) (fun g x => ?_) (hd W ν cν)
  · ext x
    simp [Representation.dual_apply, Module.Dual.transpose_apply, hν]
  · rw [hρ, smul_smul, hinv, one_smul]

end Generic

theorem isCrys_iff_of_twist : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsCrys (P.PD K) ν → (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ') := by
  intro hF l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ cν
  have h := (fontaineFormalism_iff l P).1 (GlobalTheory.RegularRing.fontaineFormalism hF l P AI ⟨T⟩) K LL
  exact isCrys_twist_iff (P.PD K) h.2.2.2.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.2.1 ρ ρ' ν χ
    (LinearMap.proj 0) (fun _ => 1) rfl hν hρ cν

end GlobalTheory.TwistCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KerGood

theorem map_aeval {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) (A : Module.End R M) (A' : Module.End R N) (hA : ∀ y, F (A y) = A' (F y))
    (p : Polynomial R) (y : M) : F (Polynomial.aeval A p y) = Polynomial.aeval A' p (F y) := by
  induction p using Polynomial.induction_on generalizing y with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c h =>
    simp only [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    rw [h (A y), hA]

theorem isGood_of_injective (hF : GlobalTheory.Published.FontaineBcris) {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a]
    {ϖ : PiSys l e} {LL : FinExt l} {Pl : LocPrime l} {AI : LocAinf l Pl} (hs : IsStd Pl AI)
    {Sig : Finset (ZMod e)} {U : Finset ℤ} {T₀ T₁ : QLat LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (hf : Function.Injective f) (he : ∀ g x, f (T₀.ρ g x) = T₁.ρ g (f x))
    (hT : IsGood a ϖ Pl T₁ Sig U) : IsGood a ϖ Pl T₀ Sig U := by
  refine ⟨?_, ?_, ?_⟩
  · have hS := (GlobalTheory.RegularRing.fontaineFormalism hF l Pl AI hs).2.2.2.1 (ϖ.field a) LL
    exact hS _ (resF T₁ (ϖ.field a)).ρ _ (resF T₀ (ϖ.field a)).ρ f (fun g x => he _ x) hf hT.crys
  · intro γ hγ w hw x hx
    obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hrf : ∀ v, r (f v) = v := fun v => LinearMap.congr_fun hr v
    have hRF : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) r
        (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, hrf]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hFi : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f) :=
      Function.LeftInverse.injective hRF
    have hFx := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB_mem (Pl.PD (ϖ.field a)) (ρ := (resF T₀ (ϖ.field a)).ρ)
      (ρ' := (resF T₁ (ϖ.field a)).ρ) (f := f) (fun g x => he _ x) x hx
    have h1 := hT.type γ hγ w hw _ hFx
    have hc : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f
        (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₀.ρ γ y) =
        actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₁.ρ γ (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, actVB, he]
      | add y z hy hz => simp only [map_add, hy, hz]
    apply hFi
    exact (map_aeval _ _ _ hc _ x).trans (h1.trans (map_zero _).symm)
  · intro τ b hb
    exact hT.jumps τ b (GlobalTheory.HTW.isJumpV_of_injective _ _ T₁.ρ f hf he τ b hb)

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  intro hF l _ a e _ _ ϖ LL _ _ Pl AI hs Sig U T₁ T₂ g hg hT
  obtain ⟨⟨_, hD, hFr⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors ↥(OL LL)) c
    refine ⟨s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, x, ?_⟩
    rw [mul_comm]
    exact hxs
  have hinj : Function.Injective (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).f := fun x y h => Subtype.ext h
  refine ⟨Formalism.MainNotions.LiftingTheory.lker_T₀ g hg hden, Formalism.MainNotions.LiftingTheory.lker_ι g hg hden, ?_,
    isGood_of_injective hF hs _ hinj (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).equiv hT⟩
  exact ⟨hinj, Formalism.MainNotions.LiftingTheory.lker_surj g hg, hg,
    fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩, fun y hy => hy⟩

end GlobalTheory.KerGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateJumpOfGaloisFixedFiltrationVector
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem mem_DdRE_qlExt {l : ℕ} [Fact l.Prime] (Pl : LocPrime l) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] (ρ : Representation LL ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)) V)
    (τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] LL) (y : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hy : y ∈ DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    y ∈ DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ τ := by
  refine Submodule.mem_inf.mpr ⟨hy, ?_⟩
  clear hy
  refine Submodule.mem_iInf _ |>.mpr fun c => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp c.2
  obtain rfl : c = algebraMap ℚ_[l] _ r := Subtype.ext hr.symm
  rw [AlgHom.commutes, algebraMap_smul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      LinearMap.mulLeft_apply]
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      TensorProduct.tmul_smul]
  | add a b ha hb => rw [map_add, ha, hb, smul_add]

theorem isJumpV_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  intro l _ Pl LL T F _ i x hfix hi hni τ
  have h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ F.1 := bot_le
  have hE : ∀ u, DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u =
      DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u := by
    intro u
    refine le_antisymm (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ fun y hy => ?_)
    exact mem_DdRE_qlExt Pl T.ρ τ y hy
  unfold IsJumpV FildR
  rw [hE, hE]
  refine (GlobalTheory.JumpDescent.jump_iff l Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F LL h T i).mp ?_
  intro heq
  have hxD : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) := by
    refine (GlobalTheory.JumpDescent.mem_DdR Pl F _ x).mpr fun g => ?_
    rw [GlobalTheory.JumpDescent.actVdR_comp Pl h]
    exact hfix _ g.2
  have hx : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
      FilV (Pl.PD F) (LL := ↥LL.1) (V := T.V) i :=
    ⟨hxD, by rw [GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hi⟩
  rw [← heq] at hx
  exact hni (by rw [← GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hx.2)

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

noncomputable section

namespace GlobalTheory.Pass.LocDual

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def locU {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  GlobalTheory.JumpDual.matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw M)
    (GlobalTheory.JumpDual.loc_cont D i w hw M hM)

def IsSummandTw (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ↥Xs) (j : X.V →ₗ[Br.LL D.nbr i w hw] (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)),
    Function.Injective j ∧
    (∀ g v, j (X.ρ g v) = fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (j v b)) ∧
    ∃ C : Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw),
      (∀ g, ∀ u ∈ C, (fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (u b)) ∈ C) ∧
      IsCompl (LinearMap.range j) C

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def DualLatLe (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (b : ℕ) : Prop :=
  ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T ≤ b

end Gen

end GlobalTheory.Pass.LocDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

theorem kummer_mem_Fq_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  intro l _ a e _ _ ϖ he k hk
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  have hr : ∀ n, ϖ.ratio k n ^ e = 1 := fun n => by
    have hmem : ϖ.seq n ^ e ∈ ϖ.Kinf := IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix _ hmem,
      div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
    rfl
  have hK : ϖ.kummer k ^ e = 1 := Perfection.ext fun n => by
    erw [map_pow, map_one]
    change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
    rw [← map_pow, hr, map_one]
  have hmem : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← he, pow_succ, hK, one_mul]
  obtain ⟨z, hz⟩ : ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k := ⟨(⟨ϖ.kummer k, hmem⟩ : ↥(resSub l a)), rfl⟩
  refine ⟨z, Fq.val_injective l a ?_, hz.symm⟩
  rw [map_pow, map_one, hz, hK]

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientToDivisibleQuotientMemCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  first | exact @GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | exact GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | (intros; apply GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D <;> assumption)
end

