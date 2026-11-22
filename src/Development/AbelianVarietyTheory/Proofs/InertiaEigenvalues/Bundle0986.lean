import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AddCharThetaLawRearrangementIdentity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCusp
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSStrict

theorem qpow (q : ℕ) (x : ℝ) : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
  simp

theorem pair_val (q : ℕ) (γ : ℂˣ) (x : ℝ) :
    (γ : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(x : ℂ)) =
      ((‖(γ : ℂ)‖ ^ 2 * (q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [qpow]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_conjU (γ : ℂˣ) : ‖((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ)‖ = ‖(γ : ℂ)‖ := by
  simp

theorem hasProd_split {ι : Type*} [DecidableEq ι] (f : ι → ℂ) (T : Finset ι) (w : ι) (hw : w ∉ T) {A B : ℂ}
    (h1 : HasProd (fun v : {v : ι // v ∉ T} => f v.1) A)
    (h2 : HasProd (fun v : {v : ι // v ∉ insert w T} => f v.1) B) : A = f w * B := by
  have h1' : HasProd ({v | v ∉ T}.mulIndicator f) A :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})).mp h1
  have h2' : HasProd ({v | v ∉ insert w T}.mulIndicator f) B :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ insert w T})).mp h2
  have h3 : HasProd (({w} : Set ι).mulIndicator f) (f w) := by
    have := hasProd_single (f := ({w} : Set ι).mulIndicator f) w (fun b hb => by simp [Set.mulIndicator_apply, hb])
    simpa using this
  have h4 := h3.mul h2'
  have heq : (fun v => ({w} : Set ι).mulIndicator f v * {v | v ∉ insert w T}.mulIndicator f v) =
      {v | v ∉ T}.mulIndicator f := by
    funext v
    by_cases hv : v = w
    · subst hv; simp [Set.mulIndicator_apply, hw]
    · by_cases hvT : v ∈ T <;> simp [Set.mulIndicator_apply, hv, hvT]
  rw [heq] at h4
  exact h1'.unique h4

theorem half_pow_le_norm_prod {α : Type*} (g : α → ℂ) (m : Multiset α) (h : ∀ p ∈ m, (1/2 : ℝ) ≤ ‖g p‖) :
    (1/2 : ℝ) ^ Multiset.card m ≤ ‖(m.map g).prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun p hp => h p (Multiset.mem_cons_of_mem hp))
    calc (1/2 : ℝ) ^ Multiset.card s * (1/2) = (1/2) * (1/2) ^ Multiset.card s := mul_comm _ _
      _ ≤ _ := mul_le_mul ha hs (by positivity) (norm_nonneg _)

theorem half_le_norm_inv_one_sub {z : ℂ} (hz : ‖z‖ < 1) : (1/2 : ℝ) ≤ ‖(1 - z)⁻¹‖ := by
  have hpos : 0 < ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simp at this; linarith
  have hle : ‖1 - z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) z
    simp at this; linarith
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos hle

def gfac (q : ℕ) (x : ℝ) (p : ℂˣ × ℂˣ) : ℂ := (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹

theorem locL_eq (q : ℕ) (B B' : Multiset ℂˣ) (x : ℝ) : locL q B B' (x : ℂ) = ((B ×ˢ B').map (gfac q x)).prod := rfl

theorem norm_sq_lt_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a →
    σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w,
      ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ _ a σ ha hσ T hT w hw α hα
  classical
  obtain ⟨L1, hL1, -, c1, hc1, hlim1⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ T hT
  have hT' : UnrOutside (insert w T) σ := fun v hv => hT v (fun h => hv (Finset.mem_insert_of_mem h))
  obtain ⟨L2, hL2, -, c2, hc2, hlim2⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ (insert w T) hT'
  have hsplit : ∀ x : ℝ, 1 < x → (L1 x : ℂ) = ((sat σ w ×ˢ (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom)).map
      (gfac (Ideal.absNorm w.asIdeal) x)).prod * (L2 x : ℂ) := by
    intro x hx
    rw [← locL_eq]
    have e := hasProd_split (ι := HeightOneSpectrum (𝓞 E)) (fun v : HeightOneSpectrum (𝓞 E) => locL (Ideal.absNorm v.asIdeal)
      (sat σ v) ((sat σ v).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) T w hw (hL1 x hx).1 (hL2 x hx).1
    exact e
  generalize hB' : (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom) = B' at hsplit
  have hmem : ∀ γ ∈ sat σ w, (γ, Units.map (starRingEnd ℂ).toMonoidHom γ) ∈ (sat σ w) ×ˢ B' := fun γ hγ =>
    Multiset.mem_product.mpr ⟨hγ, hB' ▸ Multiset.mem_map_of_mem _ hγ⟩
  generalize hqd : Ideal.absNorm w.asIdeal = q at hsplit ⊢
  have hq1 : (1 : ℝ) < q := by rw [← hqd]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith

  have hle : ∀ γ ∈ sat σ w, ‖(γ : ℂ)‖ ^ 2 ≤ (q : ℝ) := by
    intro γ hγ
    by_contra hlt
    push_neg at hlt
    have hγ0 : (0 : ℝ) < ‖(γ : ℂ)‖ ^ 2 := by
      have : (γ : ℂ) ≠ 0 := γ.ne_zero
      positivity
    have hlogq : 0 < Real.log q := Real.log_pos hq1
    set x0 := Real.log (‖(γ : ℂ)‖ ^ 2) / Real.log q with hx0def
    have hx0 : 1 < x0 := by
      rw [hx0def, lt_div_iff₀ hlogq, one_mul]
      exact Real.log_lt_log hq0 hlt
    have hpow : (q : ℝ) ^ (-x0) = (‖(γ : ℂ)‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hq0.le, Real.rpow_def_of_pos hq0]
      congr 1
      have : Real.log q * x0 = Real.log (‖(γ : ℂ)‖ ^ 2) := by
        rw [hx0def]; field_simp
      rw [this, Real.exp_log hγ0]
    have hF0 : ((sat σ w ×ˢ B').map (gfac q x0)).prod = 0 := by
      apply Multiset.prod_eq_zero
      refine Multiset.mem_map.mpr ⟨(γ, Units.map (starRingEnd ℂ).toMonoidHom γ), hmem γ hγ, ?_⟩
      simp only [gfac]
      rw [pair_val, hpow, mul_inv_cancel₀ hγ0.ne']
      simp
    have h := hsplit x0 hx0
    rw [hF0, zero_mul] at h
    have h1 := (hL1 x0 hx0).2
    have : L1 x0 = 0 := by exact_mod_cast h
    linarith
  by_contra hnot
  push_neg at hnot
  have heq : ‖(α : ℂ)‖ ^ 2 = q := le_antisymm (hle α hα) hnot
  set t : ℝ → ℝ := fun x => (q : ℝ) * (q : ℝ) ^ (-x) with ht
  have ht1 : ∀ x, 1 < x → t x < 1 := by
    intro x hx
    have : (q : ℝ) ^ (1 + -x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    rwa [Real.rpow_add hq0, Real.rpow_one] at this
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem (hmem α hα)

  have hlow : ∀ x, 1 < x → (1/2 : ℝ) ^ Multiset.card rest ≤
      (1 - t x) * ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ := by
    intro x hx
    have hspec : gfac q x (α, Units.map (starRingEnd ℂ).toMonoidHom α) = (((1 - t x : ℝ) : ℂ))⁻¹ := by
      simp only [gfac]
      rw [pair_val, heq]
      simp only [ht]
      push_cast
      ring
    have hrestb : ∀ p ∈ rest, (1/2 : ℝ) ≤ ‖gfac q x p‖ := by
      intro p hp
      have hp' : p ∈ (sat σ w) ×ˢ B' := by
        rw [hrest]; exact Multiset.mem_cons_of_mem hp
      obtain ⟨hp1, hp2⟩ := Multiset.mem_product.mp hp'
      rw [← hB'] at hp2
      obtain ⟨β, hβ, hβe⟩ := Multiset.mem_map.mp hp2
      have hb1 := hle p.1 hp1
      have hb2 := hle β hβ
      have hn2 : ‖(p.2 : ℂ)‖ = ‖(β : ℂ)‖ := by rw [← hβe]; exact norm_conjU β
      have hprod : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ q := by
        rw [hn2]
        nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(β : ℂ)‖), norm_nonneg (p.1 : ℂ), norm_nonneg (β : ℂ)]
      apply half_le_norm_inv_one_sub
      rw [qpow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
      calc ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ * (q : ℝ) ^ (-x) ≤ q * (q : ℝ) ^ (-x) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hq0.le _)
        _ < 1 := ht1 x hx
    have hpos : 0 < 1 - t x := by linarith [ht1 x hx]
    rw [hrest, Multiset.map_cons, Multiset.prod_cons, norm_mul, hspec, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    exact half_pow_le_norm_prod (gfac q x) rest hrestb

  have hnorm : ∀ x, 1 < x → ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ = ((x - 1) * L1 x) / ((x - 1) * L2 x) := by
    intro x hx
    have h := hsplit x hx
    have hL2pos : 0 < L2 x := by linarith [(hL2 x hx).2]
    have hL1pos : 0 < L1 x := by linarith [(hL1 x hx).2]
    have hFx : ((sat σ w ×ˢ B').map (gfac q x)).prod = ((L1 x / L2 x : ℝ) : ℂ) := by
      push_cast
      rw [h, mul_div_assoc, div_self (by exact_mod_cast hL2pos.ne'), mul_one]
    rw [hFx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hL1pos hL2pos),
      mul_div_mul_left _ _ (by linarith : (x - 1) ≠ 0)]
  have htlim : Tendsto t (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous t := continuous_const.mul (continuous_const.rpow continuous_neg (fun _ => Or.inl hq0.ne'))
    have := hc.tendsto 1
    simp only [ht, Real.rpow_neg_one, mul_inv_cancel₀ hq0.ne'] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hlim : Tendsto (fun x => (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x))) (𝓝[>] 1) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (hlim1.div hlim2 hc2.ne')
    simpa using this
  have hev1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x)) <
      (1/2 : ℝ) ^ Multiset.card rest := hlim (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2⟩ := (hev1.and hev2).exists
  have := hlow x hx2
  rw [hnorm x hx2] at this
  linarith

end GlobalTheory.RSStrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRows
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.FormInner

theorem ipVia_apply {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · rw [he h.1.choose_spec, he h.2.choose_spec]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem classSum_of_ad (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hrat : ∀ i, RatFrame (ad.PV i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_read (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (RatFrame.iff (hrat i)) (fun δ a b => hcV.2.1 _ a b)
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using comap_le_Umax (ad.std i) (hB i) (R.datVt i t) hκ⟩⟩ hX hFm
    hread _ hnP hip (fun _ => GlobalTheory.InvFormBdd.exists_isInvForm _ _ _)

theorem classSum_twisted (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hrat : ∀ i, RatFrame (ad.PV i))
    {tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) (v : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : TwistedAt D v) :
    ClassSum (M (D.what₂.muTw v) j h1 h2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hμ : Used0 D (D.what₂.muTw v) := Or.inr ⟨v, ((D.what₂.muAt_or v).resolve_left hv).symm⟩
  exact classSum_of_ad Y hM hB ad hrat _ hμ ⟨k, by omega⟩
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using level_le_Umax hin v ⟨k, by omega⟩ hκ⟩⟩

theorem classSum_of_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_frame (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (finite_stab_frame (hV i) (ad.std i)) (fun δ a b => hcV.2.1 _ a b)
    (comap_le_Umax (ad.std i) (hB i) (R.datVt i t)) hX hFm
    hread _ hnP hip

theorem classSum_twisted_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    {tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) (v : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : TwistedAt D v) :
    ClassSum (M (D.what₂.muTw v) j h1 h2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hμ : Used0 D (D.what₂.muTw v) := Or.inr ⟨v, ((D.what₂.muAt_or v).resolve_left hv).symm⟩
  exact classSum_of_std Y hM hB ad hV _ hμ ⟨k, by omega⟩
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using level_le_Umax hin v ⟨k, by omega⟩ hκ⟩⟩

end Gen

theorem classSum_mtL {D : D7} (L : LocAll (lay0 D)) (M : MtFam D) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (h : ClassSum (M μ j h1 h2)) : ClassSum (mtL L M μ j h1 h2) := h

theorem classSum_states : AllSt fun _ _ _ _ w P x => ∀ m : InMt x.r.Y (cfOf x) w.I.xi (QOf P), (∀ i, RatFrame (m.ad.PV i)) →
    ∀ v j h1 h2, TwistedAt (Dof x) v → ClassSum (m.M ((Dof x).what₂.muTw v) j h1 h2) := by
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all fun K B f T w _ _ _ P x m hrat v j h1 h2 hv => ?_
  obtain ⟨hB, hM⟩ : (∀ i, IsBaseFrame (Vc (Dof x) i) (x.m.z.R.βV i) (x.m.z.R.ΛV i) 1) ∧ x.m.z.R.toRealDat.IsModels := by
    refine ⟨fun i => ?_, x.m.z.pins.char.base.models⟩
    obtain ⟨c, hc⟩ := x.m.z.pins.char.base.lev.βV i
    rwa [one_pow] at hc
  exact classSum_twisted x.r.Y hM hB m.ad hrat m.mt v j h1 h2 hv

theorem exists_std_rat {D : D7} {V : HSp D} (h : GlobalTheory.StdFrame.OrthFrame V) :
    ∃ P : principalLevelFrame.RowPsi V V.rank, StdFrame (GlobalTheory.StdFrameModel.hostF_eq D) P ∧ RatFrame P :=
  ⟨_, GlobalTheory.StdFrameModel.stdPsi_unitPsi h, fun g => by simpa using GlobalTheory.NJoin.Inh.rat_unit h.gram_eq g⟩

theorem orthFrame_of_vStd {D : D7} (i : Fin D.R.m) (h : Formalism.IndefR.FWT.VStd D i) : GlobalTheory.StdFrame.OrthFrame (Vc D i) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.StdFrameCounterexample.vstd_iff i).1 h
  refine ⟨fun a b => (congrFun (congrFun h1 a) b).trans Matrix.one_apply, fun a => ?_⟩
  have := (h2 (Pi.single a 1)).2 fun b => by
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  simpa [Pi.single_apply] using this

theorem sumTw_rows : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → SumTw (w.st Z).toD7 M := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f T hO _ w _ Z Wt hX z p0 Y _ _ _ _ _ M tup Q a hin v hv j h1 h2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  obtain ⟨hB, hM⟩ : (∀ i, Formalism.IndefR.Lev.IsBaseFrame (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (z.R.βV i) (z.R.ΛV i) 1) ∧
      z.R.toRealDat.IsModels := by
    refine ⟨fun i => ?_, z.pins.char.base.models⟩
    obtain ⟨c, hc⟩ := z.pins.char.base.lev.βV i
    rwa [one_pow] at hc
  exact classSum_twisted_std Y hM hB a (fun i => orthFrame_of_vStd i (hV i)) hin v j h1 h2 hv

end GlobalTheory.FormInner

end
end

