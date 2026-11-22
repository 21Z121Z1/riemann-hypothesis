import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriedPart_eigensystem_passage_of_type : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) := by
  first | exact @GlobalTheory.Hk3.passage_of_carried | exact GlobalTheory.Hk3.passage_of_carried | (intros; apply GlobalTheory.Hk3.passage_of_carried <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusSemisimplificationWeilDeligneRestricts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem restricts_of_isFrobSS : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (X Y : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Weil h) X) (N : Module.End ℂ X) (a : WDRep h X) (ρ' : Representation ℂ (Weil h') Y) (N' : Module.End ℂ Y) (b : WDRep h' Y), IsSmooth ρ → IsSmooth ρ' → IsFrobSS ⇑ρ N a → IsFrobSS ⇑ρ' N' b → ∀ e : X ≃ₗ[ℂ] Y, (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (ρ σ x) = ρ' σ' (e x)) → (∀ x, e (N x) = N' (e x)) → Restricts (WD.mk a) (WD.mk b) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' X Y _ _ _ _ _ _ ρ N a ρ' N' b _ _ ha hb e hρ hN
  let f := (Module.finBasis ℂ X).equivFun
  let a₁ := a.transport f
  let b₀ := ResEx.resRep h h' a₁
  let g : Y ≃ₗ[ℂ] (Fin (Module.finrank ℂ X) → ℂ) := e.symm.trans f
  let ρ'' : Weil h' → Module.End ℂ (Fin (Module.finrank ℂ X) → ℂ) :=
    fun σ' => f.conjAlgEquiv ℂ (ρ (ResEx.resW h h' σ'))
  let N'' := f.conjAlgEquiv ℂ N
  have hss : IsFrobSS ρ'' N'' b₀ := by
    refine ⟨?_, fun σ' => ?_⟩
    · show f.conjAlgEquiv ℂ a.N = _
      rw [ha.1]
    · show Commute (f.conjAlgEquiv ℂ (a.ρ (ResEx.resW h h' σ'))) _ ∧ IsNilpotent (_ - f.conjAlgEquiv ℂ (a.ρ (ResEx.resW h h' σ')))
      refine ⟨(ha.2 (ResEx.resW h h' σ')).1.map (f.conjAlgEquiv ℂ), ?_⟩
      have := (ha.2 (ResEx.resW h h' σ')).2.map (f.conjAlgEquiv ℂ)
      rwa [map_sub] at this
  have hiso : b.Iso b₀ := by
    refine IsFrobSS.iso hb hss g (fun σ' y => ?_) (fun y => ?_)
    · have h1 := hρ (ResEx.resW h h' σ') σ' (fun _ => rfl) (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      show f (e.symm (ρ' σ' y)) = f.conjAlgEquiv ℂ (ρ (ResEx.resW h h' σ')) (f (e.symm y))
      rw [← h1]
      simp
    · have h1 := hN (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      show f (e.symm (N' y)) = f.conjAlgEquiv ℂ N (f (e.symm y))
      rw [← h1]
      simp
  refine ⟨_, a₁, b₀, WD.sound (a.iso_transport f).symm, (WD.sound hiso).symm, rfl, fun σ σ' hs => ?_⟩
  show a₁.ρ (ResEx.resW h h' σ') = a₁.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section
open IsNilpotent

namespace GlobalTheory.AboveL.ResWD

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem exists_tval_resI (h' : IsPlaceOver A v') (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]} {t' : Ine (F := L) A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') :
    ∃ c : Qbar l, c ≠ 0 ∧ ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ := by
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul L Ω A v' h' l hl' (t.comp ResEx.resI) t'
    (ht.1.comp ResEx.continuous_resI) ht'.1 ht'.2
  refine ⟨algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]), ?_, fun σ => ?_⟩
  swap
  · have := hc σ
    simp only [MonoidHom.comp_apply] at this
    simp [tval, this]
  intro h0
  rw [map_eq_zero, PadicInt.coe_eq_zero] at h0
  have hc0 : ∀ σ, (t (ResEx.resI (K := K) σ)).toAdd = 0 := fun σ => by
    have := hc σ
    simpa [h0] using this
  obtain ⟨σ, hσ⟩ := ht.2 (Multiplicative.ofAdd 1)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let f : ℕ → (L →ₐ[K] Ω) := fun n => (((σ : G K Ω) ^ n : G K Ω) : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω)
  have main : ∀ i j : ℕ, i < j → f i = f j → False := fun i j hij e => by
    set k := j - i with hk
    have hk0 : 0 < k := Nat.sub_pos_of_lt hij
    have hfix : ∀ x : L, ((σ : G K Ω) ^ k).toRingEquiv (algebraMap L Ω x) = algebraMap L Ω x := fun x => by
      have e1 := congrArg (fun g : L →ₐ[K] Ω => g x) e
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_algHom] at e1
      have e2 : (σ : G K Ω) ^ j = (σ : G K Ω) ^ i * (σ : G K Ω) ^ k := by
        rw [← pow_add, hk, Nat.add_sub_cancel' hij.le]
      rw [e2, AlgEquiv.mul_apply] at e1
      exact (((σ : G K Ω) ^ i).injective e1).symm
    let σ'' : G L Ω := AlgEquiv.ofRingEquiv (f := ((σ : G K Ω) ^ k).toRingEquiv) hfix
    have hres : AlgEquiv.restrictScalarsHom K σ'' = (σ : G K Ω) ^ k := AlgEquiv.ext fun _ => rfl
    have hmem : σ'' ∈ Ine (F := L) A := by
      show AlgEquiv.restrictScalarsHom K σ'' ∈ Ine (F := K) A
      rw [hres]
      exact pow_mem σ.2 k
    have e3 : ResEx.resI (K := K) ⟨σ'', hmem⟩ = σ ^ k := Subtype.ext (by rw [SubgroupClass.coe_pow, ← hres]; rfl)
    have := hc0 ⟨σ'', hmem⟩
    rw [e3, map_pow, hσ, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at this
    omega
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact main i j hlt e
  · exact main j i hlt e.symm

theorem isMonodromy_res {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    IsMonodromy t' (resTo L r) (c • N) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  refine ⟨h1.smul c, U.comap ResEx.resI, hU.preimage ResEx.continuous_resI, fun σ hσ => ?_⟩
  have := H _ hσ
  rw [smul_smul, mul_comm, ← hc]
  exact this

theorem exists_conj (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    ∃ β : Qbar l, ∀ g : Weil h', exp (β • N) * wdMat t' (deg_frob (h := h')) (resTo L r) (c • N) g =
      wdMat t (deg_frob (h := h)) r N (ResEx.resW h h' g) * exp (β • N) := by
  have hq0 : ((normV v : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV v).ne_bot
  have hf : deg (ResEx.resW h h' (frob h')) ≠ 0 := by
    intro h0
    have h1 : ((frob h' : Weil h') : G L Ω) ∈ Ine (F := L) A :=
      (deg_eq_zero_iff (σ := ResEx.resW h h' (frob h'))).1 h0
    have h2 := (deg_eq_zero_iff (σ := frob h')).2 h1
    rw [deg_frob] at h2
    exact one_ne_zero h2
  have hq1 : 1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    intro h1
    have h3 : (((normV v : ℕ) : ℚ) ^ deg (ResEx.resW h h' (frob h')) : ℚ) = 1 := by
      rw [← Rat.cast_inj (α := Qbar l)]; push_cast; exact h1
    exact hf ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _)
      (Nat.cast_ne_one.mpr (one_lt_normV v).ne')).mp h3)
  have key : ∀ m : ℤ,
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ m))⁻¹) := fun m => by
    have h1 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h'))
      (ResEx.resW h h' (frob h') ^ m)
    have h2 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)
      (ResEx.resW h h' (frob h'))
    rw [(Commute.self_zpow (ResEx.resW h h' (frob h')) m).eq] at h1
    linear_combination h2 - h1
  refine ⟨tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹), fun g => ?_⟩
  have hg : g = frob h' ^ deg g * ineIncl h' (inePart (deg_frob (h := h')) g) := by
    rw [ineIncl_inePart, mul_inv_cancel_left]
  have hRg : ResEx.resW h h' g =
      ResEx.resW h h' (frob h') ^ deg g * ineIncl h (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    conv_lhs => rw [hg]
    rw [map_mul, map_zpow, ResEx.resW_ineIncl]
  have hT : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' g)) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) +
        tval t (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    rw [hRg, ht.tval_inePart_mul hl, deg_ineIncl, zpow_zero, inv_one, one_mul, inePart_ineIncl]
  have hd : deg (ResEx.resW h h' g) = deg (ResEx.resW h h' (frob h') ^ deg g) := by
    rw [hRg, deg_mul, deg_ineIncl, add_zero]
  have hs := key (deg g)
  have hqd : ((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g) ≠ 0 := zpow_ne_zero _ hq0
  rw [wdMat, wdMat, hT]
  have e1 : (-tval t' (inePart (deg_frob (h := h')) g)) • (c • N) =
      (-tval t (ResEx.resI (inePart (deg_frob (h := h')) g))) • N := by
    rw [smul_smul, hc]
    congr 1
    ring
  have e2 : ((resTo L r g : Matrix (Fin a) (Fin a) (Qbar l))) = r (ResEx.resW h h' g) := rfl
  rw [e1, e2]
  set β := tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) with hβ
  have h2 := hN.mul_exp hl ht (ResEx.resW h h' g) ((((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g))⁻¹ * β)
  rw [mul_inv_cancel_left₀ hqd] at h2
  rw [← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have hsm : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) =
      β * (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ deg g))⁻¹) := by
    rw [hβ, div_mul_eq_mul_div, eq_div_iff hq1]
    linear_combination hs
  rw [hd]
  linear_combination hsm

end GlobalTheory.AboveL.ResWD

namespace GlobalTheory.AboveL

theorem wdOf_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)) (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal) (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal), Continuous r → Restricts (wdOf h hl ι r) (wdOf h' hl' ι (resTo L r)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι a r hl hl' hr
  have hr' : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp hr
  have ht := isTameChar_tameL h hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr'
  obtain ⟨c, hc0, hc⟩ := ResWD.exists_tval_resI h' hl' ht ht'
  have hN' := ResWD.isMonodromy_res hN hc
  obtain ⟨β, hβ⟩ := ResWD.exists_conj h h' hl ht hN hc
  obtain ⟨aK, haK⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  have ex : wdOf h hl ι r = WD.mk aK := IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, aK, hN, haK, rfl⟩
  have hb : IsFrobSS (fun g => toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)))
      (toEndC ι N) (ResEx.resRep h h' aK) := ⟨haK.1, fun g => haK.2 _⟩
  obtain ⟨aL2, haL2⟩ := hN'.exists_isFrobSS hl' ht' (deg_frob (h := h')) ι
  have hcomm : ∀ g, hN'.rep hl' ht' (deg_frob (h := h')) ι g * toEndC ι N =
      ((normV v' : ℕ) : ℂ) ^ deg g • (toEndC ι N * hN'.rep hl' ht' (deg_frob (h := h')) ι g) := fun g => by
    have := hN'.rep_comm hl' ht' (deg_frob (h := h')) ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at this
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) this
  obtain ⟨aL1, haL1⟩ := WeilDeligne.exists_isFrobSS (hN'.rep hl' ht' (deg_frob (h := h')) ι) (toEndC ι N)
    (hN'.isSmooth_rep hl' ht' _ ι) (hN.1.map _) hcomm
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul β)).map (toEndC ι (n := Fin a))
  have i1 : aL1.Iso (ResEx.resRep h h' aK) := haL1.iso hb (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι (wdMat (tameL h' hl') (deg_frob (h := h')) (resTo L r) (c • N) g)) w =
        (toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)) * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, hβ, map_mul])
    (fun w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι N) w = (toEndC ι N * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : aL1.Iso aL2 := haL1.iso_of_smul ((map_ne_zero ι).mpr hc0) (by
    have := haL2
    rw [toEndC_smul] at this
    exact this)
  have ex' : wdOf h' hl' ι (resTo L r) = WD.mk (ResEx.resRep h h' aK) :=
    (IsWDOf.wdOf_eq hl' ⟨_, ht', _, deg_frob, c • N, aL2, hN', haL2, rfl⟩).trans (WD.sound (i2.symm.trans i1))
  refine ⟨a, aK, ResEx.resRep h h' aK, ex.symm, ex'.symm, rfl, fun σ σ' hs => ?_⟩
  show aK.ρ (ResEx.resW h h' σ') = aK.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL

namespace GlobalTheory.TheRecTransport

theorem exists_contra_equiv {H H' V V' : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : H →* H') (f' : H' →* H) (hf : Continuous f) (hf' : Continuous f') (hff : ∀ g, f (f' g) = g)
    (ρ : Representation ℂ H V) (ρ' : Representation ℂ H' V') (e : V ≃ₗ[ℂ] V')
    (he : ∀ g v, e (ρ g v) = ρ' (f g) (e v)) :
    ∃ d : smoothPart ρ.dual ≃ₗ[ℂ] smoothPart ρ'.dual, ∀ g l, d (contra ρ g l) = contra ρ' (f g) (d l) := by
  have key : ∀ g (l : Module.Dual ℂ V), e.symm.dualMap (ρ.dual g l) = ρ'.dual (f g) (e.symm.dualMap l) := by
    intro g l
    ext v
    obtain ⟨v, rfl⟩ := e.surjective v
    show l (ρ g⁻¹ (e.symm (e v))) = l (e.symm (ρ' (f g)⁻¹ (e v)))
    rw [← map_inv f, ← he, e.symm_apply_apply, e.symm_apply_apply]
  have hmap : (smoothPart ρ.dual).map (e.symm.dualMap : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V') = smoothPart ρ'.dual := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((show IsOpen {g | ρ.dual g l = l} from hl).preimage hf').mem_nhds (by
          show ρ.dual (f' 1) l = l
          rw [map_one, map_one]; rfl)) fun g hg => ?_)
      have h1 : ρ.dual (f' g) l = l := hg
      show ρ'.dual g (e.symm.dualMap l) = e.symm.dualMap l
      rw [← hff g, ← key, h1]
    · intro l' hl'
      obtain ⟨l, rfl⟩ := e.symm.dualMap.surjective l'
      refine ⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((show IsOpen {g | ρ'.dual g (e.symm.dualMap l) = e.symm.dualMap l} from hl').preimage hf).mem_nhds
          (by
            show ρ'.dual (f 1) _ = _
            rw [map_one, map_one]; rfl)) fun g hg => ?_), rfl⟩
      have h1 : ρ'.dual (f g) (e.symm.dualMap l) = e.symm.dualMap l := hg
      show ρ.dual g l = l
      apply e.symm.dualMap.injective
      rw [key, h1]
  exact ⟨e.symm.dualMap.ofSubmodules _ _ hmap, fun g l => Subtype.ext (key g l)⟩

section Rep

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem exists_of_repRel {i : k ≃+* k'} {n : ℕ} (π : IrrRep (GL (Fin n) k)) {x' : IrrGL k'} (H : RepRel i (cls π) x') :
    ∃ (π' : IrrRep (GL (Fin n) k')) (e : π.V ≃ₗ[ℂ] π'.V), x' = cls π' ∧
      ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v) := by
  obtain ⟨m, π₀, π', e, h1, rfl, he⟩ := H
  obtain rfl : n = m := congrArg Sigma.fst h1
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := π.ρ) (σ := π₀.ρ) (hs := π.smooth) (hi := π.irr) (hs' := π₀.smooth)
    (hi' := π₀.irr)).1 h1
  refine ⟨π', φ.toLinearEquiv.trans e, rfl, fun g v => ?_⟩
  have h2 : φ.toLinearEquiv (π.ρ g v) = π₀.ρ g (φ.toLinearEquiv v) := φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h2, he]

theorem continuous_glMap (i : k ≃+* k') (hi : Continuous i) (n : ℕ) :
    Continuous (GeneralLinearGroup.map (n := Fin n) i.toRingHom) :=
  Continuous.units_map _ (continuous_matrix fun a b => hi.comp (continuous_id.matrix_elem a b))

theorem contra_transport (i : k ≃+* k') (hi : Continuous i) (hs : Continuous i.symm) {n : ℕ}
    (π τ : IrrRep (GL (Fin n) k)) (π' τ' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v))
    (u : τ.V ≃ₗ[ℂ] τ'.V) (hu : ∀ g v, u (τ.ρ g v) = τ'.ρ (GeneralLinearGroup.map i.toRingHom g) (u v))
    (φ : τ.ρ.Equiv (contra π.ρ)) : Nonempty (τ'.ρ.Equiv (contra π'.ρ)) := by
  obtain ⟨d, hd⟩ := exists_contra_equiv (GeneralLinearGroup.map (n := Fin n) i.toRingHom)
    (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom) (continuous_glMap i hi n) (continuous_glMap i.symm hs n)
    (map_map_symm i) π.ρ π'.ρ e he
  refine ⟨.mk (u.symm.trans (φ.toLinearEquiv.trans d)) fun g => LinearMap.ext fun v => ?_⟩
  have h2 : ∀ g v, φ.toLinearEquiv (τ.ρ g v) = contra π.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  show d (φ.toLinearEquiv (u.symm (τ'.ρ g v))) = contra π'.ρ g (d (φ.toLinearEquiv (u.symm v)))
  rw [symm_rel i τ τ' u hu, h2, hd, map_map_symm]

theorem central_transport (i : k ≃+* k') {x : IrrGL k} {x' : IrrGL k'} (H : RepRel i x x') {ω : kˣ →* ℂˣ}
    (hω : HasCentralChar x.rep ω) :
    HasCentralChar x'.rep (ω.comp (Units.map i.symm.toRingHom.toMonoidHom)) := by
  rw [← cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := exists_of_repRel _ H
  intro z v
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective v
  obtain ⟨v, rfl⟩ := e.surjective v
  have hz : GeneralLinearGroup.scalar (Fin x.1) z = GeneralLinearGroup.map i.toRingHom
      (GeneralLinearGroup.scalar (Fin x.1) (Units.map i.symm.toRingHom.toMonoidHom z)) := by
    ext a b
    by_cases hab : a = b <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal_apply, hab]
  show π'.cl.rep.ρ (GeneralLinearGroup.scalar (Fin x.1) z) (φ.toLinearEquiv (e v)) = _
  rw [← h2, hz, ← he, hω, map_smul, map_smul]
  rfl

end Rep

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem equiv_lpDual (P : PlaceIso A w A' w' φ j i) (S : WD h ≃ WD h') (hS : ∀ y y', WDRel φ y y' ↔ S y = y')
    (y : WD h) : S y.lpDual = (S y).lpDual := by
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  have hd1 : ∀ σ, deg (c.symm.toMonoidHom σ) = deg σ := fun σ => by
    have := hdegc (c.symm σ); simp only [MulEquiv.apply_symm_apply] at this
    simpa using this.symm
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth g →
      GlobalTheory.WeilDeligne.IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : GlobalTheory.WeilDeligne.IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have hF : ∀ y, S y = GlobalTheory.WDTransport.pullWD c.symm.toMonoidHom hd1 hq.symm hs1 y := fun y => by
    obtain ⟨n, b, rfl⟩ := WD.exists_rep y
    refine (hS _ _).1 ⟨n, b, GlobalTheory.WDTransport.pull c.symm.toMonoidHom hd1 hq.symm hs1 b, rfl,
      (GlobalTheory.WDTransport.pullWD_mk _ _ _ _ b).symm, rfl, fun σ σ' hσ => ?_⟩
    rw [← (hc σ σ').mp hσ]
    simp
  obtain ⟨n, b, rfl⟩ := WD.exists_rep y
  rw [hF, hF, WD.lpDual_mk, GlobalTheory.WDTransport.pullWD_mk, GlobalTheory.WDTransport.pullWD_mk, WD.lpDual_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  show b.ρ.dual (c.symm.toMonoidHom σ) v = Representation.dual (b.ρ.comp c.symm.toMonoidHom) σ v
  simp only [Representation.dual_apply, MonoidHom.comp_apply, map_inv]

end GlobalTheory.TheRecTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalRepOfReadingLaws
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RepOfLocal

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → Laws S → ∀ i, RepOfLoc D.nd D.naut i := by
  intro hL D P S hT hLaws i P₁ P₂ hsplit hns
  apply P.H.av.inj i P₁ P₂
  refine GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i P₁) (P.H.av.S i P₂) (P.H.av.irr i P₁) (P.H.av.irr i P₂) ?_ ?_
  · intro s
    have hw := GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host D s
    refine ⟨((S i s.w hw).rep P₁).toIrrRep, ((S i s.w hw).rep P₂).toIrrRep, hT.rep i s hw P₁, hT.rep i s hw P₂, ?_⟩
    have e1 := (S i s.w hw).locV P₁
    have e2 := (S i s.w hw).locV P₂
    rw [hsplit s.w hw, e2] at e1
    exact ((hLaws i s.w hw).iso _ _ _).1 e1.symm
  · intro v hv
    obtain ⟨w, hO, hns', ⟨Dv⟩⟩ := GlobalTheory.T.exists_nonsplit_place_with_inertDatum D D.R.nV v hv
    have hsph : ∀ Q : D.naut.AV i, (P.H.av.rep i Q).SphAt v := fun Q => by
      have h := D.nbc.embAV_sph i Q w hns'
      rw [P.H.emb i Q] at h
      exact (P.H.au.sph _ _ _ _ w v hns' hO).1 h
    obtain ⟨α₁, hα₁, e₁⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₁) v w hO Dv (GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical _ _ _ v w hO (hsph P₁) Dv)
    obtain ⟨α₂, hα₂, e₂⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₂) v w hO Dv (GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical _ _ _ v w hO (hsph P₂) Dv)
    have hu := hns w hns'
    rw [D.nbc.embAV_sat, D.nbc.embAV_sat, P.H.emb, P.H.emb, e₁, e₂] at hu
    refine ⟨w, Dv, α₁, hO, hα₁, ?_⟩
    obtain ⟨f, hf, hf0, U, hU, hUv, hh⟩ := hα₂
    refine ⟨f, hf, hf0, U, hU, hUv, fun h hh' => ?_⟩
    rw [GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α₁ α₂ hu h hh']
    exact hh h hh'

end GlobalTheory.RepOfLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrimeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host UpperTheory.V.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_norm_hecke_char_ramified_below_ramified_prime : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank K M = 2 → ∀ η : HChar K, IsNormChar M η → ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal → ¬ η.UnrAt (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.QuadNormRam.not_unrAt_of_ramified | exact GlobalTheory.QuadNormRam.not_unrAt_of_ramified | (intros; apply GlobalTheory.QuadNormRam.not_unrAt_of_ramified <;> assumption)
end

