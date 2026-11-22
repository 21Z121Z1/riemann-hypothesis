import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdealMapEqTransfer
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published
open scoped Pointwise

namespace GlobalTheory.FrobTransfer

theorem pow_smul_sub_mem {G S : Type} [Group G] [CommRing S] [MulSemiringAction G S] {P : Ideal S} {σ : G} {q : ℕ}
    (h : ∀ x, σ • x - x ^ q ∈ P) (n : ℕ) (x : S) : σ ^ n • x - x ^ q ^ n ∈ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := h (σ ^ n • x)
    rw [← Ideal.Quotient.eq] at h1 ih ⊢
    rw [pow_succ', mul_smul, h1, map_pow, ih, ← map_pow, ← pow_mul, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem orderOf_eq_inertiaDeg {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)} [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L} (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    orderOf σ = P.inertiaDeg (𝓞 K) := by
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : P.IsMaximal := hP.isMaximal hne
  let := Ideal.Quotient.field P
  let := Fintype.ofFinite (𝓞 L ⧸ P)
  have hc : Fintype.card (𝓞 L ⧸ P) = Ideal.absNorm 𝔭.asIdeal ^ P.inertiaDeg (𝓞 K) := by
    rw [Ideal.absNorm_pow_inertiaDeg, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hq : 1 < Ideal.absNorm 𝔭.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hf := Ideal.inertiaDeg_pos P (𝓞 K)
  apply le_antisymm
  · refine orderOf_le_of_pow_eq_one hf (hu _ ⟨P, hP, hPo, fun x => ?_⟩)
    have h1 := pow_smul_sub_mem h (P.inertiaDeg (𝓞 K)) x
    rw [← Ideal.Quotient.eq] at h1 ⊢
    rw [h1, map_pow, ← hc, FiniteField.pow_card]
  · have ho : 0 < orderOf σ := orderOf_pos σ
    have hlt : 1 < Ideal.absNorm 𝔭.asIdeal ^ orderOf σ := Nat.one_lt_pow ho.ne' hq
    have h2 := (FiniteField.forall_pow_eq_one_iff (𝓞 L ⧸ P) (Ideal.absNorm 𝔭.asIdeal ^ orderOf σ - 1)).1 fun u => by
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ P)
      have h1 := pow_smul_sub_mem h (orderOf σ) x
      rw [pow_orderOf_eq_one, one_smul, ← Ideal.Quotient.eq, map_pow, hx] at h1
      have h3 : u ^ Ideal.absNorm 𝔭.asIdeal ^ orderOf σ = u := Units.ext (by rw [Units.val_pow_eq_pow_val, ← h1])
      rw [pow_sub u hlt.le, h3, pow_one, mul_inv_cancel]
    have h4 := Nat.le_of_dvd (by omega) h2
    rw [hc] at h4
    exact (Nat.pow_le_pow_iff_right hq).1 (by omega)

omit [NumberField K] [NumberField L] in

theorem card_inertia {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] : Nat.card (P.inertia (L ≃ₐ[K] L)) = 1 := by
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => hu τ ⟨P, hP, hPo, hτ⟩
  rw [h1, Subgroup.card_bot]

theorem stabilizer_eq [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)}
    [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    Subgroup.zpowers σ = MulAction.stabilizer (L ≃ₐ[K] L) P := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have hF : IsArithFrobAt (𝓞 K) σ P := by
    unfold IsArithFrobAt AlgHom.IsArithFrobAt
    rw [← hPo.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hF.mem_stabilizer) ?_
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, one_mul,
    Nat.card_zpowers, orderOf_eq_inertiaDeg hu h]

theorem map_eq_prod [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) :
    𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) = ∏ P : 𝔭.asIdeal.primesOver (𝓞 L), P.1 := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  rw [Ideal.map_algebraMap_eq_finsetProd_pow 𝔭.ne_bot, ← Finset.prod_set_coe]
  refine Finset.prod_congr rfl fun ⟨P, hP, hPo⟩ _ => ?_
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, pow_one]

theorem heckeIdeal_prod {ι : Type} (χ : (L ≃ₐ[K] L) →* ℂˣ) (s : Finset ι) (f : ι → Ideal (𝓞 K))
    (hf : ∀ i, f i ≠ 0) : heckeIdeal L χ (∏ i ∈ s, f i) = ∏ i ∈ s, heckeIdeal L χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.NT.Model.heckeIdeal_top L χ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      GlobalTheory.NT.Model.heckeIdeal_mul L χ (hf a) (Finset.prod_ne_zero_iff.2 fun i _ => hf i), ih]

variable {N : Type} [Field N] [NumberField N] [Algebra L N] [Algebra K N] [IsScalarTower K L N]

omit [NumberField K] [NumberField L] [NumberField N] in
theorem algebraMap_restrict_smul [Normal K L] (g : N ≃ₐ[K] N) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 N) (AlgEquiv.restrictNormalHom L g • x) = g • algebraMap (𝓞 L) (𝓞 N) x :=
  RingOfIntegers.ext (g.restrictNormal_commutes L x)

omit [NumberField K] [NumberField L] [NumberField N] in
theorem under_inv_smul [Normal K L] (g : N ≃ₐ[K] N) (Q : Ideal (𝓞 N)) :
    (g⁻¹ • Q).under (𝓞 L) = (AlgEquiv.restrictNormalHom L g)⁻¹ • Q.under (𝓞 L) := by
  ext x
  rw [Ideal.mem_under, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_under,
    algebraMap_restrict_smul]

omit [NumberField K] [NumberField L] [NumberField N] in

theorem exists_restrictScalars [Normal K L] (g : N ≃ₐ[K] N) (hg : AlgEquiv.restrictNormalHom L g = 1) :
    ∃ τ : N ≃ₐ[L] N, τ.restrictScalars K = g := by
  refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => ?_, rfl⟩
  have := g.restrictNormal_commutes L x
  rw [show g.restrictNormal L = 1 from hg] at this
  exact this.symm

omit [NumberField K] [NumberField L] [NumberField N] in

theorem unramIn_top {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn N 𝔭) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] : UnramIn N P := by
  rintro τ ⟨Q, hQ, hQo, hτ⟩
  have := hu (τ.restrictScalars K) ⟨Q, hQ, Ideal.LiesOver.trans Q P.asIdeal 𝔭.asIdeal, hτ⟩
  exact AlgEquiv.ext fun x => DFunLike.congr_fun this x

omit [NumberField K] [NumberField L] [NumberField N] in

theorem minimalPeriod_eq [Normal K L] (σ : N ≃ₐ[K] N)
    (c : (N ≃ₐ[K] N) ⧸ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker) :
    Function.minimalPeriod (σ • ·) c = orderOf (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
  refine Nat.dvd_right_iff_eq.1 fun n => ?_
  rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, orderOf_dvd_iff_pow_eq_one, MulAction.Quotient.smul_mk,
    QuotientGroup.eq, MonoidHom.mem_ker, smul_eq_mul, map_mul, map_inv, map_mul, inv_mul_eq_one, mul_eq_right,
    map_pow]

theorem heckeIdeal_under [IsGalois K L] [IsGalois K N] [IsGalois L N] {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hu : UnramIn N 𝔭) {Q : Ideal (𝓞 N)} [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : N ≃ₐ[K] N}
    (h : ∀ x : 𝓞 N, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) (χ : (N ≃ₐ[L] N) →* ℂˣ) (t : N ≃ₐ[K] N)
    (τ : N ≃ₐ[L] N) (hτ : τ.restrictScalars K = t⁻¹ * σ ^ (Q.under (𝓞 L)).inertiaDeg (𝓞 K) * t) :
    heckeIdeal N χ ((t⁻¹ • Q).under (𝓞 L)) = (χ τ : ℂˣ) := by
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨(t⁻¹ • Q).under (𝓞 L), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have : P.asIdeal.LiesOver 𝔭.asIdeal := inferInstanceAs (((t⁻¹ • Q).under (𝓞 L)).LiesOver 𝔭.asIdeal)
  have := P.isPrime
  change heckeIdeal N χ P.asIdeal = _
  rw [GlobalTheory.NT.Model.heckeIdeal_prime]
  refine heckeVal_of_unramIn N χ (unramIn_top hu P) ⟨t⁻¹ • Q, inferInstance, ⟨rfl⟩, fun x => ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P.asIdeal,
    ← Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal (Q.under (𝓞 L)) (L ≃ₐ[K] L), Ideal.mem_inv_pointwise_smul_iff,
    show τ • x = τ.restrictScalars K • x from rfl, hτ, smul_sub, smul_pow', ← mul_smul, mul_assoc,
    mul_inv_cancel_left, mul_smul]
  exact pow_smul_sub_mem h _ _

theorem heckeIdeal_map_eq_transfer : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N] [IsAbelianGalois L N] (𝔭 : HeightOneSpectrum (𝓞 K)), GlobalTheory.NT.UnramIn N 𝔭 → ∀ σ : N ≃ₐ[K] N, GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ (χ : (N ≃ₐ[L] N) →* ℂˣ) (φ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker →* ℂˣ), (∀ (τ : N ≃ₐ[L] N) (h : τ.restrictScalars K ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker), φ ⟨τ.restrictScalars K, h⟩ = χ τ) → GlobalTheory.NT.heckeIdeal N χ (𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L))) = ((MonoidHom.transfer φ σ : ℂˣ) : ℂ) := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ _ 𝔭 hu σ ⟨Q, hQ, hQo, h⟩ χ φ hφ
  classical
  have huL : UnramIn L 𝔭 := GlobalTheory.RayMaximal.unramIn_of_tower hu
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L
  have hL : ∀ x : 𝓞 L, r σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q.under (𝓞 L) := fun x => by
    rw [Ideal.mem_under, map_sub, map_pow, algebraMap_restrict_smul]
    exact h _
  have hst := stabilizer_eq huL hL
  have hord := orderOf_eq_inertiaDeg huL hL
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)))
  let e : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)) → 𝔭.asIdeal.primesOver (𝓞 L) :=
    fun q => ⟨(q.out.out⁻¹ • Q).under (𝓞 L), inferInstance, inferInstance⟩
  have key : ∀ s t : N ≃ₐ[K] N, (s⁻¹ • Q).under (𝓞 L) = (t⁻¹ • Q).under (𝓞 L) ↔
      MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker) (s : (N ≃ₐ[K] N) ⧸ r.ker) t := fun s t => by
    rw [under_inv_smul, under_inv_smul, inv_smul_eq_iff, ← mul_smul, eq_comm, ← MulAction.mem_stabilizer_iff, ← hst,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨⟨σ ^ k, k, rfl⟩, ?_⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, hk, inv_mul_cancel_right,
        inv_mul_cancel]
    · rintro ⟨⟨_, k, rfl⟩, hk⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s at hk
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, inv_mul_eq_one] at hk
      exact ⟨k, by rw [← hk, mul_inv_cancel_right]⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      have := (key _ _).1 (congrArg Subtype.val hq)
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      exact Quotient.out_equiv_out.1 this
    · rintro ⟨P, hP, hPo⟩
      obtain ⟨γ, hγ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal (Q.under (𝓞 L)) P (L ≃ₐ[K] L)
      obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) N γ⁻¹
      refine ⟨Quotient.mk _ (g : (N ≃ₐ[K] N) ⧸ r.ker), Subtype.ext ?_⟩
      refine ((key _ g).2 ?_).trans (by rw [under_inv_smul, hg, inv_inv, hγ])
      rw [QuotientGroup.out_eq']
      exact Quotient.mk_out _
  rw [map_eq_prod huL, heckeIdeal_prod χ _ _ fun P => ?_, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Units.coe_prod]
  · refine (Fintype.prod_bijective e he _ _ fun q => ?_).symm
    obtain ⟨τ, hτ⟩ := exists_restrictScalars (L := L) _ (QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)
    rw [heckeIdeal_under hu h χ q.out.out τ (by rw [hτ, minimalPeriod_eq, hord]),
      ← hφ τ (hτ ▸ QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)]
    exact congrArg (fun x => ((φ x : ℂˣ) : ℂ)) (Subtype.ext hτ.symm)
  · have := P.2.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _

end GlobalTheory.FrobTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InhabitedStage
section
noncomputable section

namespace GlobalTheory.Mem.GJInhab

open Formalism.BasicNotions NumberField IsDedekindDomain

def baseVol (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : ℝ :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

theorem baseVol_pos (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : 0 < baseVol B cd W :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol_pos B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

def noJet {R : Ranks} (H : Host R) : ThetaJet R H where
  Sit := Empty
  loc := fun i => i.elim
  l_inert := fun i => i.elim
  jOf := fun i => i.elim
  j_mem := fun i => i.elim
  N0_eq := fun i => i.elim
  N1_eq_exponentN1 := fun i => i.elim
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

def oneJet {R : Ranks} (H : Host R) (hm : 1 ≤ R.m) (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l)
    (hc : H.cls l = .signal ∨ H.cls l = .inertClass) : ThetaJet R H where
  Sit := Unit
  loc := fun _ =>
    haveI : Fact l.Prime := ⟨hl⟩
    { l := l
      five_le_l := h5
      d := 2
      d_even := even_two
      two_le_d := le_rfl
      N0 := R.N 0
      N1 := R.N 1
      Th := 1 }
  l_inert := fun _ => hc
  jOf := fun _ => 1
  j_mem := fun _ => ⟨le_rfl, hm⟩
  N0_eq := fun _ => rfl
  N1_eq_exponentN1 := fun _ => rfl
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

theorem exists_noJet (B : Base) (C : Cols B) (cd : CDHaar) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = noJet B.host ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (noJet B.host) (GJModel.gxOne B) (fun i => i.elim) (fun i => i.elim)
  exact ⟨J, hcd, by rw [hv, hcd], hj, hf⟩

theorem exists_oneJet (B : Base) (C : Cols B) (cd : CDHaar) (hm : 1 ≤ B.R.m) (u : B.Word)
    (h0 : Nonempty ((C.mem u).C.cls 0)) (h1 : Nonempty ((C.mem u).C.cls 1))
    (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l) (hc : B.host.cls l = .signal ∨ B.host.cls l = .inertClass) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = oneJet B.host hm l hl h5 hc ∧
      (∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
        B.places.resChar (J.jetW i) = l) ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (oneJet B.host hm l hl h5 hc) (GJModel.gxOne B) (fun _ => ⟨u, h0, h1⟩) (fun i => i.elim)
  have key : ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 := by
    rw [hj]
    exact ⟨(), rfl, rfl, rfl⟩
  obtain ⟨i, hi1, hil, hid⟩ := key
  exact ⟨J, hcd, by rw [hv, hcd], hj, ⟨i, hi1, hil, hid, (J.jetW_l i).trans hil⟩, hf⟩

theorem nonempty_stage (B : Base) (C : Cols B) : Nonempty (GJStage B C) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  obtain ⟨J, -⟩ := exists_noJet B C cd
  exact ⟨J⟩

theorem inhabited_stage (B : Base) (C : Cols B) :
    (∃ J : GJStage B C, J.vol = baseVol B J.cd) ∧
    (1 ≤ B.R.m → Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∀ l : ℕ, l.Prime → 5 ≤ l → (B.host.cls l = .signal ∨ B.host.cls l = .inertClass) →
        ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit ∧
          ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
            B.places.resChar (J.jetW i) = l) ∧
    (Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  refine ⟨?_, fun hm h0 h1 l hl h5 hc => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨J, -, hv, -⟩ := exists_noJet B C cd
    exact ⟨J, hv⟩
  · obtain ⟨J, -, hv, -, ⟨i, hi⟩, -⟩ := exists_oneJet B C cd hm B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩, i, hi⟩
  · obtain ⟨l, hl, h5, hc⟩ := GJModel.exists_inert B.host
    have hm := B.R.two_le_m
    obtain ⟨J, -, hv, -, ⟨i, -⟩, -⟩ := exists_oneJet B C cd (by omega) B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩⟩

end GlobalTheory.Mem.GJInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGaloisOfIsRayFieldTop
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.RayTopGalois

theorem count_comap {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

section Transport

variable {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N] [NumberField N]
  [Algebra K N] [Algebra K' N] (s : K ≃+* K') (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x)

def autEquiv : (N ≃ₐ[K] N) ≃* (N ≃ₐ[K'] N) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    obtain ⟨y, rfl⟩ := s.surjective x
    rw [hs]; exact σ.commutes y
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    rw [← hs]; exact σ.commutes _
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

abbrev primeEquiv : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K') :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s)

include hs in
omit [NumberField K] [NumberField K'] [NumberField N] in
theorem liesOver_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 N)) :
    P.LiesOver (primeEquiv s 𝔭).asIdeal ↔ P.LiesOver 𝔭.asIdeal := by
  have h : ∀ x : 𝓞 K, algebraMap (𝓞 K') (𝓞 N) (RingOfIntegers.mapRingEquiv s x) = algebraMap (𝓞 K) (𝓞 N) x :=
    fun x => RingOfIntegers.ext (hs x)
  have h2 : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv s x ∈ (primeEquiv s 𝔭).asIdeal ↔ x ∈ 𝔭.asIdeal := fun x => by
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s x) ∈ 𝔭.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  refine ⟨fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩, fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩⟩
  · rw [← h2, H, Ideal.mem_under, Ideal.mem_under, h]
  · obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    rw [h2, H, Ideal.mem_under, Ideal.mem_under, h]

theorem absNorm_primeEquiv (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (primeEquiv s 𝔭).asIdeal = Ideal.absNorm 𝔭.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s) ?_).toEquiv).symm
  exact (Ideal.map_comap_of_equiv _).symm

omit [NumberField N] in
theorem isFrob_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    IsFrob N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ IsFrob N 𝔭 σ := by
  unfold IsFrob
  rw [absNorm_primeEquiv]
  exact exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

omit [NumberField K] [NumberField K'] [NumberField N] in
theorem inInertia_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    InInertia N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ InInertia N 𝔭 σ :=
  exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

theorem heckeVal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    heckeVal N χ (primeEquiv s 𝔭) = heckeVal N (χ.comp (autEquiv s hs).toMonoidHom) 𝔭 := by
  by_cases h : ∀ τ, InInertia N (primeEquiv s 𝔭) τ → χ τ = 1
  · obtain ⟨σ, hσ⟩ := exists_isFrob N 𝔭
    rw [heckeVal_eq N _ 𝔭 (fun τ hτ => h _ ((inInertia_iff' s hs 𝔭 τ).2 hτ)) hσ,
      heckeVal_eq N χ _ h ((isFrob_iff' s hs 𝔭 σ).2 hσ)]
    rfl
  · rw [heckeVal_eq_zero N χ _ h, heckeVal_eq_zero N _ 𝔭 fun h' => h fun τ hτ => ?_]
    obtain ⟨σ, rfl⟩ := (autEquiv s hs).surjective τ
    exact h' σ ((inInertia_iff' s hs 𝔭 σ).1 hτ)

theorem heckeIdeal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) {a : 𝓞 K} (ha : a ≠ 0) :
    heckeIdeal N χ (Ideal.span {RingOfIntegers.mapRingEquiv s a}) =
      heckeIdeal N (χ.comp (autEquiv s hs).toMonoidHom) (Ideal.span {a}) := by
  have e : Ideal.span {RingOfIntegers.mapRingEquiv s a} =
      (Ideal.span {a}).comap (RingOfIntegers.mapRingEquiv s).symm := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    rfl
  unfold heckeIdeal
  rw [← finprod_comp_equiv (primeEquiv s)]
  refine finprod_congr fun 𝔭 => ?_
  rw [heckeVal_transport s hs, e, count_comap _ _ (by simpa using ha)]

include hs in

theorem isModulus_top_transport [IsGalois K N] [IsGalois K' N] (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ ⊤)
    (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ ⊤ := by
  have hc : ∀ J : Ideal (𝓞 K), IsCoprime J ⊤ := fun J => by
    rw [← Ideal.one_eq_top]; exact isCoprime_one_right
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    exact (h _).2.1 𝔮 fun h => 𝔮.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _, hc _, trivial, fun φ => ?_⟩
    have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
    change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
    rwa [s.symm_apply_apply, s.symm_apply_apply] at this

include hs in
omit [NumberField K] [NumberField K'] in
theorem isAbelianGalois_transport [CharZero K] [IsAbelianGalois K N] : IsAbelianGalois K' N := by
  have : IsGalois K' N := IsGalois.of_equiv_equiv (f := s) (g := RingEquiv.refl N) (RingHom.ext hs)
  have : IsMulCommutative (N ≃ₐ[K'] N) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := (autEquiv s hs).surjective a
    obtain ⟨b, rfl⟩ := (autEquiv s hs).surjective b
    rw [← map_mul, ← map_mul, mul_comm' a b]⟩⟩
  exact {}

end Transport

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    (h : IsRayField L N ⊤) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hab := h.1
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab ⊤ ⊤ h.2 dvd_rfl top_ne_bot
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' ⊤ top_ne_bot h.2
    (@isModulus_top_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRayField_top : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L],
    GlobalTheory.Mem.Fld.IsRayField L N ⊤ → IsGalois K N := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ h
  have hab := h.1
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

end GlobalTheory.RayTopGalois

end
end

