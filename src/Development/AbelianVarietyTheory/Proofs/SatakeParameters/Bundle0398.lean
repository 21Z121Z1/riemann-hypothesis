import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0396
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0387
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0088
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.PullMap

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

theorem prod_prod_erase (g : κ → κ → ℤ) {t : Finset κ} {i : κ} (hi : i ∈ t) (hg : g i i = 1) :
    ∏ a ∈ t, ∏ b ∈ t, g a b =
      (∏ a ∈ t.erase i, ∏ b ∈ t.erase i, g a b) * ∏ a ∈ t.erase i, (g a i * g i a) := by
  have row : ∀ a, ∏ b ∈ t, g a b = g a i * ∏ b ∈ t.erase i, g a b :=
    fun a => (Finset.mul_prod_erase t (g a) hi).symm
  have h1 := Finset.mul_prod_erase t (fun a => ∏ b ∈ t, g a b) hi
  rw [← h1, row i, hg, one_mul, Finset.prod_congr rfl (fun a _ => row a)]
  simp only [Finset.prod_mul_distrib]
  ring

theorem cubeSign_eq_prod (t : Finset κ) (i : κ) :
    cubeSign t i = ∏ a ∈ t, (if a < i then (-1 : ℤ) else 1) := by
  rw [cubeSign, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem cubeSign_image {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) (i : κ) :
    cubeSign (t.image τ) (τ i) = ∏ a ∈ t, (if τ a < τ i then (-1 : ℤ) else 1) := by
  rw [cubeSign_eq_prod, Finset.prod_image (by intro x hx y hy hxy; exact h hx hy hxy)]

theorem pair_sign {τ : κ → ι} {x i : κ} (hx : x ≠ i) (hτ : τ x ≠ τ i) :
    (if x < i ∧ τ i < τ x then (-1 : ℤ) else 1) * (if i < x ∧ τ x < τ i then (-1 : ℤ) else 1) =
      (if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1) := by
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hτ with h' | h' <;>
    simp [h, h', lt_asymm h, lt_asymm h']

theorem sortSign_eq_erase {τ : κ → ι} {s : Finset κ} {i : κ} (hi : i ∈ s)
    (hne : ∀ x ∈ s.erase i, τ x ≠ τ i) :
    sortSign τ s = sortSign τ (s.erase i) *
      ∏ x ∈ s.erase i, ((if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1)) := by
  have := prod_prod_erase (fun x y => if x < y ∧ τ y < τ x then (-1 : ℤ) else 1) hi (by simp)
  beta_reduce at this
  unfold sortSign
  rw [this]
  congr 1
  exact Finset.prod_congr rfl fun x hx => pair_sign (Finset.ne_of_mem_erase hx) (hne x hx)

theorem sign_inj {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    sortSign τ t * cubeSign (t.image τ) (τ i) = cubeSign t i * sortSign τ (t.erase i) := by
  have e1 := sortSign_eq_erase (τ := τ) hi (fun x hx e =>
    Finset.ne_of_mem_erase hx (h (Finset.mem_of_mem_erase hx) hi e))
  rw [Finset.prod_mul_distrib] at e1
  have e2 : cubeSign t i = ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hi]
    simp
  have e3 : cubeSign (t.image τ) (τ i) = ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) := by
    rw [cubeSign_image h, ← Finset.mul_prod_erase t _ hi]
    simp
  have hQ : (∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1)) *
      ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => by split_ifs <;> norm_num
  rw [e1, e2, e3]
  linear_combination (sortSign τ (t.erase i) * ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1)) * hQ

theorem sign_pair {τ : κ → ι} {t : Finset κ} {a b : κ} (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) :
    cubeSign t a * sortSign τ (t.erase a) = -(cubeSign t b * sortSign τ (t.erase b)) := by
  have hb' : b ∈ t.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have ha' : a ∈ t.erase b := Finset.mem_erase.2 ⟨hab, ha⟩
  have hu' : (t.erase b).erase a = (t.erase a).erase b := Finset.erase_right_comm
  have mem : ∀ x ∈ (t.erase a).erase b, τ x ≠ τ b := by
    intro x hx e
    have hx1 := Finset.mem_erase.1 hx
    exact hx1.1 (h hx1.2 hb' e)
  have e1 := sortSign_eq_erase (τ := τ) hb' mem
  have e2 := sortSign_eq_erase (τ := τ) ha' (by rw [hu', he]; exact mem)
  rw [hu', he] at e2
  have c1 : cubeSign t a = (if b < a then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < a then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hb, ← Finset.mul_prod_erase (t.erase b) _ ha', hu']
    simp only [lt_self_iff_false, if_false, one_mul]
  have c2 : cubeSign t b = (if a < b then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < b then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ ha, ← Finset.mul_prod_erase (t.erase a) _ hb']
    simp only [lt_self_iff_false, if_false, one_mul]
  have hs : (if b < a then (-1 : ℤ) else 1) = -(if a < b then (-1 : ℤ) else 1) := by
    rcases lt_or_gt_of_ne hab with h' | h' <;> simp [h', lt_asymm h']
  rw [e1, e2, c1, c2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs]
  ring

theorem image_erase_of_injOn {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    (t.image τ).erase (τ i) = (t.erase i).image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨fun e => hy (congrArg τ e), hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxi, hx⟩, rfl⟩
    exact ⟨fun e => hxi (h hx hi e), x, hx, rfl⟩

theorem image_erase_eq {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b) (he : τ a = τ b) :
    (t.erase a).image τ = t.image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases hxa : x = a
    · exact ⟨b, ⟨hab.symm, hb⟩, by rw [hxa]; exact he.symm⟩
    · exact ⟨x, ⟨hxa, hx⟩, rfl⟩

theorem injOn_erase_swap {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) : Set.InjOn τ (t.erase b) := by
  intro x hx y hy hxy
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
  have hb' : b ∈ (↑(t.erase a) : Set κ) := by simp [hab.symm, hb]
  by_cases hxa : x = a <;> by_cases hya : y = a
  · rw [hxa, hya]
  · exact absurd (h (by simp [hya, hy.1]) hb' (by rw [← hxy, hxa, he])) hy.2
  · exact absurd (h (by simp [hxa, hx.1]) hb' (by rw [hxy, hya, he])) hx.2
  · exact h (by simp [hxa, hx.1]) (by simp [hya, hy.1]) hxy

variable {k : Type} [Field k] {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

open Classical in

theorem pullC_apply (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0 := rfl

theorem pullC_delta (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) :
    pullC τ φ (GlobalTheory.DI.delta c) = GlobalTheory.DI.delta (pullC τ φ c) := by
  funext t
  rw [pullC_apply]
  simp only [GlobalTheory.DI.delta]
  by_cases h : Set.InjOn τ t
  · rw [if_pos h, Finset.sum_image (by intro x hx y hy hxy; exact h hx hy hxy), map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [pullC_apply, if_pos (h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))), map_zsmul,
      ← image_erase_of_injOn h hi, smul_smul, smul_smul, sign_inj h hi]
  · rw [if_neg h]
    have h' : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (by intro x hx y hy hxy; exact hc x hx y hy hxy)
    obtain ⟨a, ha, b, hb, he, hab⟩ := h'
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → pullC τ φ c s = 0 := fun s has hbs => by
      rw [pullC_apply, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩), smul_zero])]
    by_cases hia : Set.InjOn τ (t.erase a)
    · have hib := injOn_erase_swap hb hab he hia
      rw [pullC_apply, pullC_apply, if_pos hia, if_pos hib, image_erase_eq hb hab he,
        image_erase_eq ha hab.symm he.symm, smul_smul, smul_smul, ← add_smul, sign_pair ha hb hab he hia,
        neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ (t.erase b) := fun hib => hia (injOn_erase_swap ha hab.symm he.symm hib)
      rw [pullC_apply, pullC_apply, if_neg hia, if_neg hib, smul_zero, smul_zero, add_zero]

theorem pullC_mem (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E')
    (hφ : ∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) (n : ℤ) (c : Finset ι → E)
    (hc : c ∈ cechC A n) : pullC τ φ c ∈ cechC B n := by
  simp only [cechC, Submodule.mem_pi, Set.mem_univ, true_implies, forall_const] at hc ⊢
  intro s
  rw [pullC_apply]
  split_ifs with hs hinj
  · have hcard := Finset.card_image_of_injOn hinj
    have hc' := hc (s.image τ)
    rw [if_pos ⟨hs.1.image τ, by rw [hcard]; exact hs.2⟩] at hc'
    exact zsmul_mem (hφ s hs.1 _ hc') _
  · exact Submodule.zero_mem _
  · rename_i hinj
    have hc' := hc (s.image τ)
    rw [if_neg (fun h' => hs ⟨Finset.image_nonempty.1 h'.1, by
      rw [← Finset.card_image_of_injOn hinj]; exact h'.2⟩), Submodule.mem_bot] at hc'
    rw [hc', map_zero, smul_zero]
    exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

end GlobalTheory.PD.PullMap

namespace GlobalTheory.PD

theorem pullC_isMap : ∀ (k : Type) [Field k] (ι κ : Type) [LinearOrder ι] [LinearOrder κ] (E E' : Type)
    [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E'),
    (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) →
    (∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) → IsMap (cech A) (cech B) (pullC τ φ) := by
  intro k _ ι κ _ _ E E' _ _ _ _ A B τ φ _ _ hφ n c hc
  exact ⟨PullMap.pullC_mem A B τ φ hφ n c hc, PullMap.pullC_delta τ φ c⟩

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusGoodOfSelfDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist UpperTheory.V UpperTheory.V.Af ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem loc_eq_unrChar [IsTotallyComplex E] (χ : HChar E) (hu : χ.UnrAt w) :
    χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
  refine MonoidHom.ext fun x => ?_
  have h2 := unif_spec w
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 := hu _ h1
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem satWD_map_mul (h : Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) (c : ℂˣ)
    {art : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h art)
    (hs : GlobalTheory.WeilDeligne.IsSmooth ((SmGL.unrChar (w.adicCompletion E) c).comp art)) :
    satWD h a (B.map (· * c)) = (satWD h a B).lpTwist _ hs := by
  have hM : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp art) hs =
      WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := Test.lpOfChar_unrChar ha c hs
  have hMu : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).unr := (WD.unr_mk _).mpr (WDRep.unr_diag _)
  have hMf : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)} := by
    rw [WD.frobEig_diag]; simp
  have h0 : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  obtain ⟨hu0, hf0, -⟩ := WD.lpUnr_spec (h := h) _ h0
  have hU : WD.lpUnr h ((B.map (· * c)).map fun b => ((b⁻¹ : ℂˣ) : ℂ)) =
      (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpChar (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)) := by
    have hu1 := WD.unr_lpChar _ _ hu0 hMu
    rw [WD.unr_eq_lpUnr _ hu1, WD.frobEig_char _ _ _ hu0 hMu hMf, hf0, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [mul_inv_rev, mul_comm]
  rw [← lpChar_lpOfChar, hM, satWD, satWD, GlobalTheory.NuShift.lpChar_lpTw, hU]

end GlobalTheory.RoadU.PhiTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist GlobalTheory.RoadU.PhiTwist UpperTheory.V UpperTheory.V.Af in

theorem GlobalTheory.RoadU.holdsS_good_phi : Inputs → SphericalLevelCondition .csd .crys → SphericalLevelCondition .csd .phi → SphericalLevelCondition .good .phi := by
  intro hI Hc Hp E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w hw B hB
  intro P AI hT A h O _ _ _ Bw hj g
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.GoodCsdTwist.exists_goodCsd_twist GlobalTheory.automorphicFormsFiniteGL E l a ha π χ hS w hw
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  have hκ' := isAlgPos_of_isAlg hκ
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι κ m hκ'
  have hcont : Continuous (tw r μ) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc
  have hr' : Weak (π.twist κ) ι (tw r μ) := ⟨hcont, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := CG.HasSat.twist hB hu
  have C : (wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)).charPol g =
      (satWD h a (B.map (· * κ.val w))).charPol g :=
    Hp E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj g
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  have hsph : SmGL.IsSpherical σ.ρ :=
    GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.isSpherical_of_hasSatGL w a (((GlobalTheory.Cong.satake_locComp E a π w σ hσ).1 B).1 hB)
  have c1 : IsCrysAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    Hc E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj _ (hσ.twist κ)
      (GlobalTheory.CrysTwistBack.isSpherical_twist_of_unr a w σ κ hu hsph)
  obtain ⟨T⟩ := hT
  have c1s : IsSstAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI ⟨T⟩ E Ω _ O Bw a _ c1
  have hμi : IsCrysAt P Bw ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ⁻¹ (-m) μ⁻¹
      (GlobalTheory.GalChar.isAlgPos_inv hκ') hμc.inv hL.inv w A h O Bw hj).2.2.1 hu.inv
  have hrr : r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype = Formalism.MainNotions.SumRepresentations.At.twGL ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, GlobalTheory.TripleGal.rk1, Matrix.det_unique, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_apply]
  have hct : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp (hcont.comp continuous_subtype_val)
  have hcμi : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.inv.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hsst : IsSstAt P Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    rw [hrr]
    exact isSstAt_twist hI.pst P AI ⟨T⟩ Bw _ _ hct hcμi c1s hμi
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  have hdet : Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
      = μ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype := by
    ext g
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
  have htw : (tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.twGL (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
        (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  have hcR : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      ((r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp (hr.1.comp continuous_subtype_val)
  have hcμ : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hdR := (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj).1
  have hPμ := GlobalTheory.Published.DeRhamPotSemistable.isPstAt hI.pst T Bw _ hcμ hdR
  have hP := isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ hsst
  have hP' := isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ c1s
  rw [htw] at hP'
  have hWD : wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) =
      (wdAt P ι Bw h hj (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)).lpTwist ((κ.loc w).comp a') (ha'.smooth hc.1) := by
    rw [htw, GlobalTheory.TwistParamAbove.wdAt_twist l P AI ⟨T⟩ ι E Ω A w h O Bw hj a _ _ hcR hcμ hP hPμ hP',
      hI.alg E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj _ hc a' ha', lpChar_lpOfChar]
  have hsat : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth (ξ.comp a')),
      ξ = SmGL.unrChar (w.adicCompletion E) (κ.val w) →
      satWD h a (B.map (· * κ.val w)) = (satWD h a B).lpTwist _ hξ := by
    rintro ξ hξ rfl
    exact satWD_map_mul h a B (κ.val w) ha' hξ
  rw [hWD, hsat (κ.loc w) (ha'.smooth hc.1) (loc_eq_unrChar κ hu)] at C
  exact (charPol_lpTwist_iff _ _ _ _ g).1 C

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermCompatId
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.W1.Lef

def GermCompat {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) (ψ : Z.functionField → Y.functionField) : Prop :=
  ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
    ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g)

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in

theorem _root_.GlobalTheory.W1.Lef.germCompat_id (Z : Scheme.{0}) [IsIntegral Z] :
    _root_.GlobalTheory.W1.Lef.GermCompat (𝟙 Z) (fun y => y) := by
  intro V hV hV' g
  rfl

abbrev omCx {K : Type} [Field K] [Algebra ℂ K] {ι : Type} [LinearOrder ι] (B : Finset ι → Subalgebra ℂ K) (a : ℕ) :
    Cx ℂ (Finset ι → DR ℂ K) := GlobalTheory.PD.cech fun I => omB ℂ K (B I) a

def mapL (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] :
    DR ℂ K →ₗ[ℂ] DR ℂ L := (mapDR ℂ K L).toLinearMap.restrictScalars ℂ

theorem mapL_apply (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    (ω : DR ℂ K) : mapL K L ω = mapDR ℂ K L ω := rfl

def mixMul {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (φ₂ φ₁ : DR ℂ K →ₗ[ℂ] DR ℂ L) :
    DR ℂ K →ₗ[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ L := (LinearMap.mul ℂ (DR ℂ L)).compl₁₂ φ₂ φ₁

def mixCover {Z Y : Scheme.{0}} {ι : Type} [LinearOrder ι] (c1 c2 : Y ⟶ Z) (U : ι → Z.Opens) : ι ×ₗ ι → Y.Opens :=
  fun S => c2 ⁻¹ᵁ U (fstL S) ⊓ c1 ⁻¹ᵁ U (sndL S)

abbrev CmpFam : Type 1 :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [Smooth p] [Algebra ℂ X.functionField] (ι : Type) [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (B : Finset ι → Subalgebra ℂ X.functionField), IsAffCover p U B →
    ∀ a b : ℕ, hodgeH p a b ≃ₗ[ℂ] (omCx B a).H b

def NatPull (e : CmpFam) : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [Smooth p] [Algebra ℂ X.functionField] (ι : Type) [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (B : Finset ι → Subalgebra ℂ X.functionField) (hU : IsAffCover p U B)
    (X' : Scheme.{0}) [IsIntegral X'] (p' : X' ⟶ Sp ℂ) [Smooth p'] [Algebra ℂ X'.functionField] (ι' : Type) [LinearOrder ι']
    [Fintype ι'] (U' : ι' → X'.Opens) (B' : Finset ι' → Subalgebra ℂ X'.functionField) (hU' : IsAffCover p' U' B')
    (f : X' ⟶ X) (hf : f ≫ p = p') (ψ : X.functionField →ₐ[ℂ] X'.functionField)
    (φ : DR ℂ X.functionField →ₗ[ℂ] DR ℂ X'.functionField) (τ : ι' → ι),
    IsDRMap ℂ ψ φ → GermCompat f ψ → (∀ i, U' i ≤ f ⁻¹ᵁ U (τ i)) →
    ∀ (a b : ℕ) (z : hodgeH p a b) (c : (omCx B a).Z b) (c' : (omCx B' a).Z b),
      e X p ι U B hU a b z = Submodule.Quotient.mk c →
      e X' p' ι' U' B' hU' a b (hodgePull hf a b z) = Submodule.Quotient.mk c' →
      c'.1 - pullC τ φ c.1 ∈ (omCx B' a).B b

def NatTrace (e : CmpFam) : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [Smooth p] [Algebra ℂ X.functionField] (ι : Type) [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (B : Finset ι → Subalgebra ℂ X.functionField) (hU : IsAffCover p U B)
    (X' : Scheme.{0}) [IsIntegral X'] (p' : X' ⟶ Sp ℂ) [Smooth p'] [Algebra ℂ X'.functionField]
    (f : X' ⟶ X) [IsFinite f] [Etale f] (hf : f ≫ p = p') (B' : Finset ι → Subalgebra ℂ X'.functionField)
    (hU' : IsAffCover p' (fun i => f ⁻¹ᵁ U i) B')
    [Algebra X.functionField X'.functionField] [IsScalarTower ℂ X.functionField X'.functionField],
    GermCompat f (algebraMap X.functionField X'.functionField) →
    ∀ (a b : ℕ) (z : hodgeH p' a b) (c : (omCx B a).Z b) (c' : (omCx B' a).Z b),
      e X' p' ι (fun i => f ⁻¹ᵁ U i) B' hU' a b z = Submodule.Quotient.mk c' →
      e X p ι U B hU a b (hodgeTrace hf a b z) = Submodule.Quotient.mk c →
      c.1 - trC c'.1 ∈ (omCx B a).B b

def locTerm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℕ) : ℂ :=
  (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a / (1 - A).det

example (A : Matrix (Fin 0) (Fin 0) ℂ) : locTerm A 0 = 1 := by simp [locTerm]

end GlobalTheory.W1.Lef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureOfFiniteMapIntegrallyClosedSubrinStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_of_finite_map_integrallyClosed_subrings : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  first | (exact @GlobalTheory.W1.integralClosure_of_finite_map) | (exact GlobalTheory.W1.integralClosure_of_finite_map) | (intros; apply GlobalTheory.W1.integralClosure_of_finite_map  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegrallyClosedSectionsOfSmoothComplexStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  first | (exact @GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (exact GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (intros; apply GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominatorStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_span_cotangent_change_denominator : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ∀ (n : ℕ), 0 < n →
    ∀ (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ) (a b : MvPolynomial (Fin (N + 1)) ℂ)
      (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
      (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
      (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
      (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b)),
      RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2 →
      RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  first | (exact @GlobalTheory.EtProj.span_ratio_of_span_ratio) | (exact GlobalTheory.EtProj.span_ratio_of_span_ratio) | (intros; apply GlobalTheory.EtProj.span_ratio_of_span_ratio  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLocalModelsOfSplitUnramifiedJointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  first | exact @GlobalTheory.TwV.modelsOK_of_joints | exact GlobalTheory.TwV.modelsOK_of_joints | (intros; apply GlobalTheory.TwV.modelsOK_of_joints <;> assumption)
end

