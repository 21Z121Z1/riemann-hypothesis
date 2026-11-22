import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDEqSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeRecon

section SlopeTestRemainingChoices
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_rt {W : Type} [AddCommGroup W] [Module ℂ W] (h h' : GAf L n) (f : GAf L n → W) :
    NG.rt L n h' (NG.rt L n h f) = NG.rt L n (h' * h) f := by
  funext g
  change f (g * h' * h) = f (g * (h' * h))
  rw [mul_assoc]

theorem rt_one {W : Type} [AddCommGroup W] [Module ℂ W] (f : GAf L n → W) : NG.rt L n 1 f = f := by
  funext g
  change f (g * 1) = f g
  rw [mul_one]

theorem finite_cosets (N' : ℕ) (hN' : 0 < N') :
    {c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N' | ∃ x : GAf L n, x ∈ Umax L n ∧
      (x : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') = c}.Finite := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L) N' hN'
  haveI := hQ
  let cls : Umax L n → Fin n → Fin n → Q := fun κ i j => c ⟨(κ.1.1 : Matrix (Fin n) (Fin n) (AL L)) i j, κ.2 i j⟩
  have key : ∀ a b : Umax L n, cls a = cls b →
      ((a.1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') = (b.1 : GAf L n) := by
    intro a b hab
    rw [QuotientGroup.eq]
    exact GlobalTheory.IsotOrth.cong_inv_mul a.2 b.2 (fun i j => by
      obtain ⟨z, hz⟩ := hc _ _ (congrFun (congrFun hab i) j).symm
      refine ⟨z.1, z.2, ?_⟩
      simpa using congrArg Subtype.val hz)
  let F : (Fin n → Fin n → Q) → GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N' := fun q =>
    if h : ∃ a, cls a = q then ((h.choose.1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') else ((1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N')
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨cls ⟨x, hx⟩, ?_⟩
  have h : ∃ a, cls a = cls ⟨x, hx⟩ := ⟨_, rfl⟩
  simp only [F, dif_pos h]
  exact key _ _ h.choose_spec

open Classical in
theorem heckeD_eq_sum {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (f : GAf L n → W) (g : GAf L n) :
    NG.heckeD J D f g = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then f (g * hc.choose) else 0) := by
  unfold NG.heckeD
  rw [finsum_eq_sum_of_support_subset]
  intro c hc
  rw [Set.Finite.coe_toFinset]
  by_contra h
  exact hc (dif_neg h)

theorem heckeD_add {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (f f' : GAf L n → W) :
    NG.heckeD J D (f + f') = NG.heckeD J D f + NG.heckeD J D f' := by
  funext g
  rw [Pi.add_apply, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem heckeD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (a : ℂ) (f : GAf L n → W) :
    NG.heckeD J D (a • f) = a • NG.heckeD J D f := by
  funext g
  rw [Pi.smul_apply, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem heckeD_zero {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n)) :
    NG.heckeD J D (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem heckeD_one {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (v : GAf L n → W)
    (hv : ∀ κ ∈ J, NG.rt L n κ v = v) :
    NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * 1 * u'} v = v := by
  funext g
  unfold NG.heckeD
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ J)]
  · have h : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * 1 * u'},
        (x : GAf L n ⧸ J) = ((1 : GAf L n) : GAf L n ⧸ J) :=
      ⟨1, ⟨1, J.one_mem, 1, J.one_mem, by simp⟩, rfl⟩
    rw [dif_pos h]
    obtain ⟨⟨u, hu, u', hu', e⟩, -⟩ := h.choose_spec
    rw [e]
    have : u * 1 * u' ∈ J := by simpa using J.mul_mem hu hu'
    exact congrFun (hv _ this) g
  · intro c hc
    rw [dif_neg]
    rintro ⟨x, ⟨u, hu, u', hu', rfl⟩, hx⟩
    apply hc
    rw [← hx, QuotientGroup.eq]
    have : u * 1 * u' ∈ J := by simpa using J.mul_mem hu hu'
    simpa using J.inv_mem this

end SlopeTestRemainingChoices

theorem recon : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a b : NG.AlgWt L n) (S₁ : Submodule ℂ (GAf L n → a.W)) (S₂ : Submodule ℂ (GAf L n → b.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep b.ρ S₂ → ∀ N : ℕ, 0 < N → ∀ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → b.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) → (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n a b S₁ S₂ hS₁ hS₂ N hN φ hφ hex hT
  obtain ⟨f₀, hf₀S, hf₀fix, hf₀ne⟩ := hex
  set J := GlobalTheory.IsotOrth.congSub L n N with hJ
  let gens : Set ((GAf L n → a.W) × (GAf L n → b.W)) :=
    {w | ∃ (h : GAf L n) (f : GAf L n → a.W), f ∈ S₁ ∧ (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧
      w = (NG.rt L n h f, NG.rt L n h (φ f))}
  let W := Submodule.span ℂ gens
  have hgen : ∀ (h : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) →
      (NG.rt L n h f, NG.rt L n h (φ f)) ∈ W := fun h f hf hfix => Submodule.subset_span ⟨h, f, hf, hfix, rfl⟩
  have hWS : ∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂ := by
    intro w hw
    have : W ≤ S₁.prod S₂ := by
      rw [Submodule.span_le]
      rintro _ ⟨h, f, hf, hfix, rfl⟩
      exact ⟨hS₁.1.stable h f hf, hS₂.1.stable h _ (hφ f hf hfix).1⟩
    exact this hw
  have hWst : ∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W := by
    intro h w hw
    have : W ≤ W.comap ((NG.rt L n h).prodMap (NG.rt L n h)) := by
      rw [Submodule.span_le]
      rintro _ ⟨h', f, hf, hfix, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.prodMap_apply, rt_rt, rt_rt]
      exact hgen _ f hf hfix
    exact this hw
  have hfinE : ∀ M', 0 < M' → {c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M') |
      ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M')) = c}.Finite := by
    intro M' hM'
    refine (finite_cosets (N * M') (Nat.mul_pos hN hM')).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (show NG.Cong L n N x from hx).1, rfl⟩
  let P : ((GAf L n → a.W) × (GAf L n → b.W)) → Prop := fun w => ∃ M : ℕ, 0 < M ∧ ∀ M', 0 < M' → M ∣ M' →
    NG.heckeD (GlobalTheory.IsotOrth.congSub L n (N * M')) (J : Set (GAf L n)) w.2 =
      φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n (N * M')) (J : Set (GAf L n)) w.1)
  let Good : Submodule ℂ ((GAf L n → a.W) × (GAf L n → b.W)) :=
    { carrier := {w | P w}
      zero_mem' := ⟨1, one_pos, fun M' _ _ => by simp [heckeD_zero]⟩
      add_mem' := by
        rintro w w' ⟨M, hM, hw⟩ ⟨M₁, hM₁, hw'⟩
        refine ⟨M * M₁, Nat.mul_pos hM hM₁, fun M' hM' hd => ?_⟩
        have h1 := hw M' hM' (dvd_trans (dvd_mul_right M M₁) hd)
        have h2 := hw' M' hM' (dvd_trans (dvd_mul_left M₁ M) hd)
        simp only [Prod.fst_add, Prod.snd_add]
        rw [heckeD_add _ _ (hfinE M' hM'), heckeD_add _ _ (hfinE M' hM'), h1, h2, map_add]
      smul_mem' := by
        rintro c w ⟨M, hM, hw⟩
        refine ⟨M, hM, fun M' hM' hd => ?_⟩
        simp only [Prod.smul_fst, Prod.smul_snd]
        rw [heckeD_smul _ _ (hfinE M' hM'), heckeD_smul _ _ (hfinE M' hM'), hw M' hM' hd, map_smul] }
  have hWG : W ≤ Good := by
    rw [Submodule.span_le]
    rintro _ ⟨h, f, hf, hfix, rfl⟩
    obtain ⟨M, hM, hMc⟩ := GlobalTheory.T.exists_deeper_congruence_conj_into_congruence L n N h hN
    refine ⟨M, hM, fun M' hM' hd => ?_⟩
    obtain ⟨k, rfl⟩ := hd
    have hconj : ∀ κ ∈ GlobalTheory.IsotOrth.congSub L n (N * (M * k)), h⁻¹ * κ * h ∈ J := by
      intro κ hκ
      rw [← mul_assoc] at hκ
      exact hMc κ (NG.Cong.of_mul_left L n hκ)
    have hle : GlobalTheory.IsotOrth.congSub L n (N * (M * k)) ≤ J := fun κ hκ => NG.Cong.of_mul_left L n hκ
    obtain ⟨m, -, hmE⟩ := GlobalTheory.T.doubleCosetOperator_translate_deeper_level_eq_smul L n J (GlobalTheory.IsotOrth.congSub L n (N * (M * k))) h hle hconj (hfinE _ hM')
    have hfixJ : ∀ κ ∈ J, NG.rt L n κ f = f := fun κ hκ => hfix κ hκ
    have hφfixJ : ∀ κ ∈ J, NG.rt L n κ (φ f) = φ f := fun κ hκ => (hφ f hf hfix).2 κ hκ
    show NG.heckeD _ _ (NG.rt L n h (φ f)) = φ (NG.heckeD _ _ (NG.rt L n h f))
    rw [hmE _ f hfixJ, hmE _ (φ f) hφfixJ, map_smul, hT h f hf hfix]
  have hWP : ∀ w ∈ W, P w := fun w hw => hWG hw
  have hK2 : ∀ u, ((0 : GAf L n → a.W), u) ∈ W → u = 0 := by
    let K : Submodule ℂ (GAf L n → b.W) := W.comap (LinearMap.inr ℂ _ _)
    have hKsub : NG.IsSubrep b.ρ K := ⟨fun u hu => hS₂.1.le (hWS _ hu).2, fun h u hu => by
      have := hWst h _ hu
      simpa [K] using this⟩
    have hKle : K ≤ S₂ := fun u hu => (hWS _ hu).2
    rcases hS₂.2.2 K hKsub hKle with hK | hK
    · intro u hu
      have : u ∈ K := hu
      rwa [hK, Submodule.mem_bot] at this
    · exfalso
      have hmem : φ f₀ ∈ K := hK ▸ (hφ f₀ hf₀S hf₀fix).1
      obtain ⟨M, hM, hMg⟩ := hWP _ (Submodule.mem_comap.1 hmem)
      have e := hMg M hM dvd_rfl
      obtain ⟨m, hm, hmE⟩ := GlobalTheory.T.doubleCosetOperator_translate_deeper_level_eq_smul L n J (GlobalTheory.IsotOrth.congSub L n (N * M)) 1
        (fun κ hκ => NG.Cong.of_mul_left L n hκ)
        (fun κ hκ => by rw [inv_one, one_mul, mul_one]; exact NG.Cong.of_mul_left L n hκ) (hfinE M hM)
      have hφfixJ : ∀ κ ∈ J, NG.rt L n κ (φ f₀) = φ f₀ := fun κ hκ => (hφ f₀ hf₀S hf₀fix).2 κ hκ
      have e2 := hmE _ (φ f₀) hφfixJ
      rw [rt_one, heckeD_one J _ hφfixJ] at e2
      simp only [LinearMap.inr_apply, heckeD_zero, map_zero] at e
      rw [e] at e2
      apply hf₀ne
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      exact (smul_eq_zero.1 e2.symm).resolve_left hm'
  have hK1 : ∀ u, (u, (0 : GAf L n → b.W)) ∈ W → u = 0 := by
    let K : Submodule ℂ (GAf L n → a.W) := W.comap (LinearMap.inl ℂ _ _)
    have hKsub : NG.IsSubrep a.ρ K := ⟨fun u hu => hS₁.1.le (hWS _ hu).1, fun h u hu => by
      have := hWst h _ hu
      simpa [K] using this⟩
    have hKle : K ≤ S₁ := fun u hu => (hWS _ hu).1
    rcases hS₁.2.2 K hKsub hKle with hK | hK
    · intro u hu
      have : u ∈ K := hu
      rwa [hK, Submodule.mem_bot] at this
    · exfalso
      have hmem : f₀ ∈ K := hK ▸ hf₀S
      have h1 : (f₀, (0 : GAf L n → b.W)) ∈ W := hmem
      have h2 := hgen 1 f₀ hf₀S hf₀fix
      rw [rt_one, rt_one] at h2
      have h3 := W.sub_mem h2 h1
      simp only [Prod.mk_sub_mk, sub_self, sub_zero] at h3
      exact hf₀ne (hK2 _ h3)
  refine GlobalTheory.T.equivariant_iso_of_translationStable_graph L n a.ρ b.ρ S₁ S₂ W hS₁ hS₂ hWS hWst hK2 hK1 ?_
  intro hbot
  have := hgen 1 f₀ hf₀S hf₀fix
  rw [hbot, Submodule.mem_bot, rt_one, rt_one] at this
  exact hf₀ne (congrArg Prod.snd this)

end GlobalTheory.HeckeRecon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorBilinear
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

namespace GlobalTheory.InertHeckeLin

open Classical in
theorem heckeFunI_bilinear : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ (c : ℂ) (f f' : GAf L n → W), heckeFunI L n U Dv (h + h') f = heckeFunI L n U Dv h f + heckeFunI L n U Dv h' f ∧ heckeFunI L n U Dv (c • h) f = c • heckeFunI L n U Dv h f ∧ heckeFunI L n U Dv h (f + f') = heckeFunI L n U Dv h f + heckeFunI L n U Dv h f' ∧ heckeFunI L n U Dv h (c • f) = c • heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU W _ _ h hh h' hh' c f f'
  have hfin : ∀ k ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
      (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval k (Dv.loc x) ≠ 0} := fun k hk =>
    GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hU k hk
  have hsupp : ∀ k ∈ Hecke ℂ (KU Dv.σw n), ∀ (φ : GAf L n → W) (g : GAf L n),
      (Function.support (fun c : GAf L n ⧸ U =>
        if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
          Dv.hval k (Dv.loc hc.choose) • φ (g * hc.choose) else 0)).Finite := by
    intro k hk φ g
    refine (hfin k hk).subset ?_
    intro c hc
    simp only [Function.mem_support] at hc
    split_ifs at hc with h1
    · refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
      intro h0
      rw [h0, zero_smul] at hc
      exact hc rfl
    · exact absurd rfl hc
  have hadd : ∀ y, Dv.hval (h + h') y = Dv.hval h y + Dv.hval h' y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  have hsmul : ∀ y, Dv.hval (c • h) y = c * Dv.hval h y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h' hh' f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hadd, add_smul]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hsmul, mul_smul]
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h hh f' g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [smul_add]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs
    · exact smul_comm _ _ _
    · rw [smul_zero]

end GlobalTheory.InertHeckeLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesRightTranslationStabl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

namespace GlobalTheory.HeckeStab

theorem heckeFunI_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (GAf L n → W)), (∀ g, ∀ f ∈ S, NG.rt L n g f ∈ S) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f ∈ S, heckeFunI L n U Dv h f ∈ S := by
  classical
  intro L _ _ _ n v w Dv U hUv W _ _ S hS h hh f hf
  have hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0} :=
    GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hUv h hh
  have key : heckeFunI L n U Dv h f = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        Dv.hval h (Dv.loc hc.choose) else 0) •
      NG.rt L n (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        hc.choose else 1) f := by
    funext g
    unfold heckeFunI
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · simp only [dif_pos hc]
        rfl
      · simp only [dif_neg hc, zero_smul]
        rfl
    · intro c hc0
      rw [Function.mem_support] at hc0
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · rw [dif_pos hc] at hc0
        rw [Set.Finite.coe_toFinset]
        refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
        rw [h0, zero_smul]
      · exact absurd (dif_neg hc) hc0
  rw [key]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hS _ f hf)

end GlobalTheory.HeckeStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertHeckeLift

theorem dualC_single {d : List ℤ} (hd : dualLab d = d) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single d 1 := by
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single, hd]

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, Module.End.one_apply, hk, Units.val_one, one_smul] at h2

theorem csum_adj {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (Gr → W)) (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y))
    (jm : S.Forms → M.H) (hj : ∀ f, M.e (jm f) = P.ext f.1) (U : Module.End K S.Forms) (u : Module.End ℂ M.H)
    (hu : LinearMap.adjoint u = u) (hU : ∀ f, jm (U f) = u (jm f)) (f g : S.Forms) :
    S.csum (U f).1 g.1 = S.csum f.1 (U g).1 := by
  have hin : ∀ f g : S.Forms, inner ℂ (jm f) (jm g) = σ (S.csum f.1 g.1) := by
    intro f g
    rw [hM.2.2, hj, hj]
    exact (GlobalTheory.classPres_basic ι S σ ρ J χ P).2.1 f g
  apply σ.injective
  rw [← hin, ← hin, hU, hU, ← LinearMap.adjoint_inner_right, hu]

theorem tie_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {I : Type} {pl : I → Pl D.host.E}
    {ty : I → List ℤ} {op : I → Module.End K S.Forms} {inR : I → Prop}
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op inR (fun i => IsLabElt V (pl i) (ty i)) (fun i => IsLocElt V (pl i)))
    (i : I) (hi : inR i) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i))
    (hpw : (ty i).Pairwise (fun a b => b ≤ a)) :
    IsLab V (pl i) (ty i) ∧ ∀ f : S.Forms, Pr.ext (op i f).1 = hkF V (pl i) (Finsupp.single (ty i) 1) (Pr.ext f.1) := by
  obtain ⟨c, hc⟩ := hβ
  rw [one_pow] at hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl i).isPrime.ne_top
  have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc (pl i) h1 hoff (ty i) (Comparison₂.hx i) (Comparison₂.hA i) hpw
    (Comparison₂.hx_ok i hi) (Comparison₂.hA_loc i hi) (Comparison₂.hDC i hi)
  exact ⟨hd.1, fun f => (Comparison₂.op_eq i hi f).trans (hd.2 W _ fun g k hk => ext_mul Pr f g k (Comparison₂.chi_loc i hi k hk))⟩

theorem inert_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ j t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtCSD j t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j t).pres op inR (fun i => IsLabElt (Vc D j) (pl i) (ty i)) (fun i => IsLocElt (Vc D j) (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtCSD j t).Forms, (A.MtCSD j t).csum ((op i f : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V) (g : (A.MtCSD j t).Cl → (A.MtCSD j t).V) = (A.MtCSD j t).csum (f : (A.MtCSD j t).Cl → (A.MtCSD j t).V) ((op i g : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V)) ∧ IsLab (Vc D j) (pl i) (ty i) ∧ ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM j t I pl ty op inR hin Comparison₂ i hi
  have hgood := (hin i hi).1
  have hd := tie_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres Comparison₂ i hi hgood (hin i hi).2.2
  have hj : ∀ f : (A.MtCSD j t).Forms, (R.HV j t).e (R.jV j t f) = (R.B.L j t).pres.ext f.1 := fun f => hM.jV j t f
  have hint : ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) :=
    fun h hh f => (hM.HV j t).1 (((hj _).trans (hd.2 f)).trans
      ((congrArg (hkF (Vc D j) (pl i) (Finsupp.single (ty i) 1)) (hj f).symm).trans (hh (pl i) hgood _ _).symm))
  refine ⟨GlobalTheory.HeckeRational.lifts_dcOp_mem_cmMax R hF.tie j t (Comparison₂.hA i) (op i) (Comparison₂.op_eq i hi), ?_, hd.1, hint⟩
  refine ((GlobalTheory.T.realization_family_normal_operators R F hL hF hM).2 j t).elim fun h hh => ?_
  have hdual : dualLab (ty i) = ty i := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) (pl i) (ty i)).1 hd.1).2.2 (hin i hi).2.1
  have hadj := (hh.2.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans (congrArg (h (pl i)) (dualC_single hdual))
  exact csum_adj (R.B.L j t).pres (R.HV j t) (hM.HV j t) (fun f => R.jV j t f) hj (op i) _ hadj (hint h hh.1)

end GlobalTheory.InertHeckeLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLocalIntegralOfMemLatticeStabilizer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmaxInt

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

omit [IsCMField L] in

theorem compAt_mem_tensInt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {x : AL L}
    (hx : x ∈ ALint L) :
    compAt L v x ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, GlobalTheory.InertUmax.compAt_tmul]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, GlobalTheory.InertUmax.compAt_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨a v, ha v⟩, rfl⟩)
  exact key hx

end GlobalTheory.InertUmaxInt

open GlobalTheory.InertUmaxInt in

theorem GlobalTheory.InertUmaxInt.loc_integral_of_mem_Umax : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ u : GAf L n, u ∈ Umax L n → ∀ i j, ((Dv.loc u : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L) := by
  intro L _ _ _ n v w Dv u hu i j
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have he : ∀ k l, Dv.e (compAt L v ((u.1 : Matrix (Fin n) (Fin n) (AL L)) k l)) ∈
      intL (w.adicCompletion L) := fun k l =>
    (Dv.integ _).1 (compAt_mem_tensInt L v (hu k l))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (he l k)) (hP k j)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIsoStatement
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)), IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  first | exact @GlobalTheory.SerSys.irrSm_pullback | exact GlobalTheory.SerSys.irrSm_pullback | (intros; apply GlobalTheory.SerSys.irrSm_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfBlockTypeVectorPadicIsoStatement
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (ξ : Fˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ), TamePart (ξ.comp (Units.map e.toMonoidHom)) χ → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), GlobalTheory.SplitRead.IsBlockVec ξ ρ u → IsParVec (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) r t χ u := by
  first | exact @GlobalTheory.ParRead.isParVec_of_isBlockVec | exact GlobalTheory.ParRead.isParVec_of_isBlockVec | (intros; apply GlobalTheory.ParRead.isParVec_of_isBlockVec <;> assumption)
end

