import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0467
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationV
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.PiSys

theorem iD_const_Ehat_eq_tmul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ϖ.iD t K (fun _ => Ehat O K l e) = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
  rw [iD, glue_const, Ehat, iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))

end GlobalTheory.BKReal.PiSys

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime]

theorem ev_eis_assoc_xi {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {ε : Per.Fl l} (hE : GlobalTheory.MemLoc.IsEps ε) :
    (∃ c : Per.Ainf l, c * GlobalTheory.MemLoc.xi ε = ϖ.ev a (eis l a e)) ∧
      ∃ c' : Per.Ainf l, c' * ϖ.ev a (eis l a e) = GlobalTheory.MemLoc.xi ε := by
  have hsp := (ϖ.span_ev_eis a).trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  refine ⟨Ideal.mem_span_singleton'.1 ?_, Ideal.mem_span_singleton'.1 ?_⟩
  · rw [← hsp]; exact Ideal.mem_span_singleton_self _
  · rw [hsp]; exact Ideal.mem_span_singleton_self _

theorem isUnit_and_mem_FilD_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Per.BdR l), x ∈ Per.FilD l j ↔
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ Per.FilD l (j + 1) := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := ev_eis_assoc_xi (a := a) ϖ hE
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hU : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hα : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c) * (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc]
  have hβ : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) = (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc']
  refine ⟨IsUnit.of_mul_eq_one
    (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) ?_, ?_⟩
  · rw [← mul_assoc, mul_comm _ (algebraMap _ _ (GlobalTheory.MemLoc.aDp l c')), hβ, Units.mul_inv]
  intro j x
  rw [GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, ← hUdef]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c * w, ?_⟩
    rw [hα, _root_.zpow_add_one, Units.val_mul, map_mul]
    ring
  · rintro ⟨w, hw⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c' * w, ?_⟩
    have h2 : (U : Per.BdR l) * x = (U : Per.BdR l) * (((U ^ j : (Per.BdR l)ˣ) : Per.BdR l) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c' * w)) := by
      calc (U : Per.BdR l) * x = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x) := by
              rw [← mul_assoc, hβ]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (((U ^ (j + 1) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w) := by rw [hw]
        _ = _ := by rw [_root_.zpow_add_one, Units.val_mul, map_mul]; ring
    exact U.isUnit.mul_left_cancel h2

variable {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)

theorem isUnit_and_mem_Fil_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (K : FinExt l) :
    IsUnit (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔
        GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ (Pl.PD K).Fil (j + 1) := by
  obtain ⟨hu, hF⟩ := isUnit_and_mem_FilD_iff (l := l) (a := a) ϖ
  have hc : Td.eD (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) :=
    RingEquiv.apply_symm_apply _ _
  refine ⟨?_, fun j x => ?_⟩
  · have := hu.map (Td.eD.symm : Per.BdR l →+* Pl.R.BdR)
    rw [← hc] at this
    simpa using this
  · rw [Td.fil, Td.fil, map_mul, hc]
    exact hF j _

section Abstract

variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem map_mem_FilV (K : FinExt l) (j k : ℤ) (g : Pl.R.BdR →ₗ[ℚ_[l]] Pl.R.BdR)
    (hg : ∀ b ∈ (Pl.PD K).Fil j, g b ∈ (Pl.PD K).Fil k) (x : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hx : x ∈ FilV (Pl.PD K) (LL := LL) (V := V) j) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g x ∈ FilV (Pl.PD K) (LL := LL) (V := V) k := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨g b.1, hg _ b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add]; exact Submodule.add_mem _ hy hz

theorem map_mulLeft_comp (r s : Pl.R.BdR) (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] r)
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] s) x) =
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (r * s)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp [mul_assoc]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem map_mulLeft_one (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (1 : Pl.R.BdR)) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

end Abstract

end GlobalTheory.BKReal.EhatShift

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem bijective_and_mem_FilV_iff_of_mul (K : FinExt l) (ξ : Pl.R.BdR) (hu : IsUnit ξ)
    (hF : ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔ ξ * x ∈ (Pl.PD K).Fil (j + 1))
    (f : V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR) (hf : ∀ v c, f (v ⊗ₜ[ℚ_[l]] c) = v ⊗ₜ[ℚ_[l]] (ξ * c)) :
    Function.Bijective f ∧ ∀ (y : V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ),
      y ∈ FilV (Pl.PD K) (LL := LL) (V := V) j ↔ f y ∈ FilV (Pl.PD K) (LL := LL) (V := V) (j + 1) := by
  have hAM : ∀ y, f y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] ξ) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v c => rw [hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hl : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (f y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.val_inv_mul, map_mulLeft_one]
  have hr : ∀ y, f (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.mul_val_inv, map_mulLeft_one]
  refine ⟨Function.bijective_iff_has_inverse.2 ⟨_, hl, hr⟩, fun y j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hAM]
    exact map_mem_FilV K j (j + 1) _ (fun b hb => (hF j b).1 hb) y h
  · have := map_mem_FilV K (j + 1) j
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (fun b hb => by
        rw [hF j, LinearMap.mulLeft_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
        exact hb) _ h
    rwa [hl] at this

end GlobalTheory.BKReal.EhatShift

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  intro l _ a e _ _ ϖ LL _ _ T Pl AI Td A hA
  rw [GlobalTheory.BKReal.PiSys.iD_const_Ehat_eq_tmul l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ]
  obtain ⟨hu, hF⟩ := GlobalTheory.BKReal.EhatShift.isUnit_and_mem_Fil_iff Td (a := a) ϖ (Formalism.MainNotions.ElementDenominator.qlExt l)
  refine GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff_of_mul _ _ hu hF _ fun v c => ?_
  rw [hA]
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.IBInj

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
  [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
  [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]

omit [NeZero a] [NeZero e] [Module.Finite ℤ_[l] O] [CompleteSpace K] in

theorem toOB_injective : Function.Injective (toOB l O) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := O) (acrisToBcris l).toLinearMap
    (GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l)

omit [NeZero a] in

theorem iSD_eq_of_mem_invL_A (ϖ : PiSys l e) (f : invL l (S O K e)) (hf : (f : K⟦X⟧) ∈ invL l (A O K)) :
    ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
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

omit [NeZero a] in

theorem crisToOD_iS (ϖ : PiSys l e) (s : S O K e) : crisToOD l O (ϖ.iS O K s) =
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ
  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) =
      crisToOD l O (ϖ.iS O K s) := fun s => ϖ.iSD_of_mem O K s.2 _
  rw [← sub_eq_zero]
  set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
  have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
    simp only [hD, map_add]; ring
  have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
    simp only [hD, map_mul, map_pow, map_natCast]; ring
  have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
    intro m
    obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ m
    have hw : ∀ k : ℕ, ∃ y : OA l O,
        ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
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
        exact iSD_eq_of_mem_invL_A ϖ _ hPA
      obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
      obtain ⟨y2, hy2⟩ := GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd l e O K ϖ m hS'
      refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
      have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k *
            toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
          (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') -
            toOD l O y1) - (l : OD l O) ^ N * ((l : OD l O) ^ m *
              ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
        rw [hsP, hDadd, hDP, zero_add, hDmul]
        simp only [hD, map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e1]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
    have h1 := GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ m _ hw
    rw [pow_add, mul_assoc] at h1
    exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
  have hc := ϖ.complete_OD O K
  exact hc.toIsHausdorff.haus' _ fun n => by
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
    exact Ideal.mem_span_singleton.2 (hdiv n)

omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NeZero e] [CompleteSpace K] in

theorem eq_zero_of_forall_dvd (x : Ahat O K l e) (h : ∀ n : ℕ, ∃ y, x = Ehat O K l e ^ n * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, rfl⟩ := h n
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) = Ideal.Quotient.mk _ (EIn l e _) :=
    AlgHom.commutes _ _
  rw [map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul]
  exact (map_zero _).symm

theorem eq_zero_of_idem_mul_iS (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (τ : ZMod a) (s : S O K e)
    (h : idem (constC t) τ * ϖ.iS O K s = 0) : s = 0 := by
  set x := toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s) with hx
  have h1 : idem (constD t) τ * ϖ.iHat O K x = 0 := by
    have h2 := congrArg (crisToOD l O) h
    rw [map_mul, map_zero, crisToOD_iS ϖ s] at h2
    have h3 : crisToOD l O (idem (constC t) τ) = idem (constD t) τ :=
      crisToOD_toOCr (constA t (Pi.single τ 1))
    rwa [h3] at h2
  have h4 : ϖ.iD t K (Pi.single τ x) = 0 := by
    rw [PiSys.iD, glue_apply, Finset.sum_eq_single τ (fun σ _ hσ => by
      rw [Pi.single_eq_of_ne hσ, map_zero, mul_zero]) (by simp), Pi.single_eq_same, h1]
  have h5 : x = 0 := eq_zero_of_forall_dvd x fun n => by
    obtain ⟨y, hy⟩ := GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ n (Pi.single τ x)
      (by rw [h4]; exact zero_mem _)
    exact ⟨y τ, by simpa using congrFun hy τ⟩
  have h6 : toHat O K l e ⟨(s : K⟦X⟧), invL_S_le_Rpi l e (le_away _ _ s.2)⟩ = 0 := h5
  have h7 := GlobalTheory.BK.toHat_injective O K l e (h6.trans (map_zero _).symm)
  have h8 : (s : K⟦X⟧) = 0 := congrArg (fun z : Rpi O K l e => (z : K⟦X⟧)) h7
  exact Subtype.ext h8

theorem iB_injective (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) : Function.Injective (ϖ.iB t K) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => funext fun τ => ?_
  obtain ⟨k, hk⟩ := (x τ).2
  set s : S O K e := ⟨_, hk⟩
  have hs : algebraMap (S O K e) (invL l (S O K e)) s = (l : invL l (S O K e)) ^ k * x τ :=
    Subtype.ext (by simp [s])
  have h1 := idem_mul_glue (constB t) (ϖ.iSl O K) x τ
  rw [show glue (constB t) (ϖ.iSl O K) x = 0 from hx, mul_zero] at h1
  have h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s) :=
    ϖ.iSl_of_mem O K s.2 _
  have h2 : toOB l O (idem (constC t) τ * ϖ.iS O K s) = 0 := by
    rw [map_mul, ← h3, hs, map_mul, map_pow, map_natCast]
    change idem (constB t) τ * (_ * _) = 0
    rw [mul_left_comm, ← h1, mul_zero]
  have h4 : idem (constC t) τ * ϖ.iS O K s = 0 := toOB_injective (h2.trans (map_zero _).symm)
  have h5 := eq_zero_of_idem_mul_iS t ϖ τ s h4
  have h6 : (l : invL l (S O K e)) ^ k * x τ = 0 := by rw [← hs, h5, map_zero]
  have h7 : (l : K⟦X⟧) ^ k * (x τ : K⟦X⟧) = 0 := by simpa using congrArg Subtype.val h6
  have hl0 : (l : K⟦X⟧) ≠ 0 := fun h0 => BK.l_ne_zero (K := K) l (by
    simpa using congrArg PowerSeries.constantCoeff h0)
  exact Subtype.ext ((mul_eq_zero.1 h7).resolve_left (pow_ne_zero _ hl0))

theorem iB_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l)
    (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) :=
  fun _ _ _ _ _ _ _ t ϖ => iB_injective t ϖ

end GlobalTheory.BKReal.IBInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLiftPeriodPowSmulIntertwiner
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.PoleBound

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l}

theorem frobW_per (hτ : bk.IsPer τ) : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ := by
  rw [frobW_inclW, hτ.1, map_mul]; rfl

theorem exists_basis {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.a • T := by
  have key : ∀ r j, inclW l τ ^ S.a * T r j ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.a * T r j)
      (Matrix.of fun j i => bk.ev (S.A i j)) fun j => by
        have e := congrFun (congrFun h.φ r) j
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.a), mul_assoc, e, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (S.A i j) * _
        ring
  choose t ht using key
  exact ⟨Matrix.of t, Matrix.ext fun r j => ht r j⟩

theorem exists_inv {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T U : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) (hU : U * T = 1) (hT : T * U = 1) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.b • U := by
  have h1 : U.map (frobW l) * T.map (frobW l) = 1 := by
    rw [← Matrix.map_mul (f := frobW l), hU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul (f := bk.evW), S.A_mul]
    ext1 i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : bk.evW bk.E ^ S.b • U.map (frobW l) = bk.evW bk.E ^ S.a • (S.A'.map bk.evW * U) := by
    have e := congrArg (fun M => U.map (frobW l) * (M * S.A'.map bk.evW) * U) h.φ
    simp only [Matrix.mul_assoc T, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, hT, Matrix.mul_one] at e
    exact e.symm
  have key : ∀ r j, inclW l τ ^ S.b * U j r ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.b * U j r)
      (Matrix.of fun j i => bk.ev (bk.E ^ S.a * S.A' j i)) fun j => by
        have e := congrFun (congrFun h3 j) r
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.b), mul_assoc, e, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (bk.E ^ S.a * S.A' j i) * _
        rw [map_mul, map_pow]
        ring
  choose t ht using key
  exact ⟨Matrix.of fun j r => t r j, Matrix.ext fun j r => ht r j⟩

theorem exists_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ (f : Matrix (Fin d') (Fin d) ℤ_[l]) (X : Matrix (Fin d') (Fin d) (WCb l)), T' * X = zW f * T →
    ∃ (M : ℕ) (x : Matrix (Fin d') (Fin d) (Ainf l)), x.map (inclW l) = inclW l τ ^ M • X := by
  intro l _ K bk τ hτ d d' S S' ρ ρ' T T' h h' f X hX
  obtain ⟨V, hV⟩ := h'.unit
  have hU : (V⁻¹ : _ˣ).1 * T' = 1 := hV ▸ V.inv_mul
  have hT : T' * (V⁻¹ : _ˣ).1 = 1 := hV ▸ V.mul_inv
  obtain ⟨t, ht⟩ := exists_basis hτ h
  obtain ⟨u, hu⟩ := exists_inv hτ h' hU hT
  have hf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f :=
    Matrix.ext fun i j => (inclWA l).commutes (f i j)
  refine ⟨S'.b + S.a, u * (f.map (algebraMap ℤ_[l] (Ainf l)) * t), ?_⟩
  rw [Matrix.map_mul, Matrix.map_mul, ht, hu, hf, Matrix.mul_smul, ← hX, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc, hU, Matrix.one_mul, smul_smul, pow_add]

end GlobalTheory.BSP.PoleBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMap
section
set_option synthInstance.maxHeartbeats 400000

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.BKGal.CrisTensDR

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
  {LL : FinExt l} (T : QLat LL)

theorem coe_smul_lat (o : ↥(OL LL)) (x : ↥T.L.T) :
    ((o • x : ↥T.L.T) : T.V) = (o : ↥LL.1) • (x : T.V) := by
  rw [Submodule.coe_smul]
  exact (algebraMap_smul (↥LL.1) o (x : T.V)).symm

def gx (o : ↥(OL LL)) (b : Per.Bcris l) : ↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR :=
  AddMonoidHom.mk' (fun x => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (fun x y => by
      simp only [Submodule.coe_add, smul_add, TensorProduct.add_tmul])

def gb (o : ↥(OL LL)) : Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun b => gx Td T o b)
    (fun b c => by
      ext x
      simp only [gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, TensorProduct.tmul_add])

def g : ↥(OL LL) →+ Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun o => gb Td T o)
    (fun o o' => by
      ext b x
      simp only [gb, gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Subalgebra.coe_add, add_smul,
        TensorProduct.add_tmul])

theorem cB_smul (z : ℤ_[l]) (b : Per.Bcris l) :
    GlobalTheory.BKGal.JumpDR.cB Td (z • b) = (z : ℚ_[l]) • GlobalTheory.BKGal.JumpDR.cB Td b := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.BKGal.JumpDR.cB_algebraMap, ← Algebra.smul_def]

theorem zsmul_lat (z : ℤ_[l]) (o : ↥(OL LL)) (x : ↥T.L.T) :
    (((z • o : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (z : ℚ_[l]) • ((o : ↥LL.1) • (x : T.V)) := by
  show ((z : ℚ_[l]) • (o : ↥LL.1)) • (x : T.V) = _
  exact smul_assoc _ _ _

theorem g_balanced (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.Bcris l) : g Td T (z • o) b = g Td T o (z • b) := by
  ext x
  have h1 := congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (zsmul_lat T z o x)
  have h2 := congrArg (fun w => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] w) (cB_smul Td z b)
  exact h1.trans ((TensorProduct.smul_tmul _ _ _).trans h2.symm)

def f1 : OB l ↥(OL LL) →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  TensorProduct.liftAddHom (g Td T) (g_balanced Td T)

theorem mul_smul_lat (o o' : ↥(OL LL)) (x : ↥T.L.T) :
    (((o * o' : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (o' : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
  rw [coe_smul_lat, smul_smul, Subalgebra.coe_mul, mul_comm]

theorem crisTensorDRLiftFromCoeffBcris_smul_comm (o : ↥(OL LL)) :
    (f1 Td T).comp (DistribMulAction.toAddMonoidHom (OB l ↥(OL LL)) o) =
      (AddMonoidHom.compHom' (DistribMulAction.toAddMonoidHom (↥T.L.T) o)).comp (f1 Td T) := by
  refine AddMonoidHom.ext fun u => ?_
  induction u using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul o' b =>
    refine AddMonoidHom.ext fun x => ?_
    show g Td T (o * o') b x = g Td T o' b (o • x)
    exact congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (mul_smul_lat T o o' x)
  | add u v hu hv => exact (map_add _ u v).trans ((congrArg₂ (· + ·) hu hv).trans (map_add _ u v).symm)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  intro l _ Pl AI Td LL T
  exact ⟨TensorProduct.liftAddHom (f1 Td T) fun o u x =>
    DFunLike.congr_fun (DFunLike.congr_fun (crisTensorDRLiftFromCoeffBcris_smul_comm Td T o) u) x, fun o b x => rfl⟩

end GlobalTheory.BKGal.CrisTensDR
end
end

