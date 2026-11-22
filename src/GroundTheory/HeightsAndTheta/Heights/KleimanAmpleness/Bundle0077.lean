import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotPartEqGradedPiece
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc cechZc cechBc cechCc locPart quotPart Cell cellMon)

noncomputable section

theorem quotPart_eq_gradedPiece {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (hm : ∀ k, 0 ≤ m k) :
    quotPart F V m = NumbersDVR.gradedPiece V (fun k => (m k).toNat) := by
  have hset : {p : MvPolynomial (Σ k, ι k) F | (∀ k, 0 ≤ m k) ∧ IsMultiHomog p (fun k => (m k).toNat)} =
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) (fun k => (m k).toNat) : Set _) := by
    ext p
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_weightedHomogeneousSubmodule, hm, implies_true, true_and]
    exact (Bridge.isMultiHomog_iff p _).symm
  rw [quotPart, hset, NumbersDVR.gradedPiece]
  conv_rhs => rw [← Submodule.span_eq (weightedHomogeneousSubmodule F _ _), Submodule.map_span]
  rfl

theorem isMultiHomog_one {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRingOver S ι) 0 := by
  intro d hd k
  classical
  rw [mem_support_iff, coeff_one] at hd
  split_ifs at hd with h
  · subst h
    simp
  · exact absurd rfl hd

theorem MultiSerre.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hI : SectionMapInj.Statement) :
    MultiSerre.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hV' : IsMultiHomogIdeal V := (Bridge.isMultiHomogIdeal_iff V).mp hV
  have hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.IsMGraded F ι (quotPart F V) :=
    HilbertSamuel.QuotPartGraded.proof F K ι V hV'
  obtain ⟨-, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩, -⟩ :=
    hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  obtain ⟨c₃, h₃⟩ := hI F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  filter_upwards [eventually_ge_atTop (fun _ : K => max (max c₁ c₂) (max c₃ 0))] with m hm
  have hk : ∀ k, max (max c₁ c₂) (max c₃ 0) ≤ m k := fun k => hm k
  refine ⟨fun i hi => h₁ m i hi fun k => le_trans (by omega) (hk k), ?_⟩

  let Z := cechZc ι (quotPart F V) m 0
  have hmem : ∀ x ∈ quotPart F V m, (fun _ => LocalizedModule.mk x 1 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechC F ι
      (MvPolynomial (Σ k, ι k) F ⧸ V) 0) ∈ Z := by
    intro x hx
    refine HilbertSamuel.GenTwistGenerated.mem_cechZc_zero (fun J => ?_)
      (HilbertSamuel.GenTwistGenerated.cechD_const x)
    refine Submodule.subset_span ⟨x, 1, 0, isMultiHomog_one, ?_, rfl⟩
    convert hx using 2
    ext k
    simp
  let φ : quotPart F V m →ₗ[F] Z :=
    { toFun := fun x => ⟨fun _ => LocalizedModule.mk x.1 1, hmem x.1 x.2⟩
      map_add' := fun x y => by
        ext I
        simp
      map_smul' := fun r x => by
        ext I
        simp [LocalizedModule.smul'_mk] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hsub : x.1 - y.1 = 0 := by
      refine h₃ m (fun k => le_trans (by omega) (hk k)) _ (Submodule.sub_mem _ x.2 y.2) fun I => ?_
      have h := congrFun (congrArg Subtype.val hxy) I
      change LocalizedModule.mk x.1 1 = LocalizedModule.mk y.1 1 at h
      change LocalizedModule.mkLinearMap (cellMon F I.1) _ (x.1 - y.1) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hzx⟩ := h₂ m (fun k => le_trans (by omega) (hk k)) z hz
    exact ⟨⟨x, hx⟩, Subtype.ext (funext fun I => (hzx I).symm)⟩
  have hbot : (cechBc ι (quotPart F V) m 0).comap (cechZc ι (quotPart F V) m 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  have e2 : cechHc ι (quotPart F V) m 0 ≃ₗ[F] Z := Submodule.quotEquivOfEqBot _ hbot
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_trans (by omega) (hk k)
  rw [e2.finrank_eq, ← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, NumbersDVR.hilbFn, if_pos hm0,
    quotPart_eq_gradedPiece V m hm0]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RatioMonHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

noncomputable section

section Ratio

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def ResidueGen.ratioMon (β : K → ℤ) (c d : ∀ k, ι k) : MRingOver F ι :=
  ∏ k, (X ⟨k, d k⟩ ^ (β k).toNat * X ⟨k, c k⟩ ^ (-β k).toNat)

theorem ResidueGen.ratioMon_homog (β : K → ℤ) :
    ∃ a : K → ℕ, ∀ c d : ∀ k, ι k, IsMultiHomog (ResidueGen.ratioMon (F := F) β c d) a := by
  classical
  refine ⟨_, fun c d => ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_prod _ _ _ fun k _ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_mul
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (d k)) _)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (c k)) _)⟩

omit [∀ k, Fintype (ι k)] in
theorem ResidueGen.aeval_ratioMon {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) =
      ∏ k, (z ⟨k, d k⟩ ^ (β k).toNat * z ⟨k, c k⟩ ^ (-β k).toNat) := by
  simp [ResidueGen.ratioMon, map_prod]

omit [∀ k, Fintype (ι k)] in

theorem ResidueGen.ratio_eval {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hd : ∀ k, z ⟨k, d k⟩ ≠ 0) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) / aeval z (ResidueGen.ratioMon (F := F) β d c) =
      (∏ k, z ⟨k, c k⟩ ^ (-β k)) / ∏ k, z ⟨k, d k⟩ ^ (-β k) := by
  rw [ResidueGen.aeval_ratioMon, ResidueGen.aeval_ratioMon, ← Finset.prod_div_distrib,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hck := hc k
  have hdk := hd k
  conv_rhs => rw [← Int.toNat_sub_toNat_neg (β k)]
  rw [neg_sub, zpow_sub₀ hck, zpow_sub₀ hdk]
  simp only [zpow_natCast]
  field_simp

end Ratio

theorem ResidueGen.proof : ResidueGen.Statement := by
  intro F _ K _ ι _ Ω _ _ y K' _ _ y' _ R σ hσ hchart β hgen d₀ hd₀
  classical

  have hne : ∀ p : Σ k, ι k, y' p ≠ 0 → y p ≠ 0 := by
    rintro ⟨k, a⟩ hp h0
    obtain ⟨hm, he⟩ := hσ (X ⟨k, a⟩) (X ⟨k, a⟩) _ (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a) (by simpa [aeval_X] using hp)
    have h0' : (⟨_, hm⟩ : R) = 0 := Subtype.ext (by simp [aeval_X, h0])
    rw [h0', map_zero, aeval_X, div_self hp] at he
    exact zero_ne_one he
  have hy0 : ∀ k, y ⟨k, d₀ k⟩ ≠ 0 := fun k => hne _ (hd₀ k)
  have hG0' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  have hG0 : (∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy0 k)
  obtain ⟨ext, ext_eq⟩ : ∃ e : Ω → K', ∀ z (hz : z ∈ R), e z = σ ⟨z, hz⟩ :=
    ⟨fun z => if hz : z ∈ R then σ ⟨z, hz⟩ else 0, fun z hz => dif_pos hz⟩
  obtain ⟨a, ha⟩ := ResidueGen.ratioMon_homog (F := F) (ι := ι) β

  have key : ∀ h ∈ secOver F y β, ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∃ hh : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R,
        σ ⟨_, hh⟩ = ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) *
          ∏ k, y' ⟨k, c k⟩ ^ (-β k) := by
    intro h hH c hc'
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
    obtain ⟨h0R, -⟩ := hchart d₀ hd₀ _ ((PowRealises.mem_secOver y β h).mp hH d₀ hy0)
    obtain ⟨hrR, hr⟩ := hσ (ResidueGen.ratioMon β c d₀) (ResidueGen.ratioMon β d₀ c) a (ha c d₀) (ha d₀ c)
      (by
        rw [ResidueGen.aeval_ratioMon]
        exact Finset.prod_ne_zero_iff.mpr fun k _ =>
          mul_ne_zero (pow_ne_zero _ (hc' k)) (pow_ne_zero _ (hd₀ k)))
    have eqΩ := ResidueGen.ratio_eval (F := F) y β c d₀ hc hy0
    have eqK := ResidueGen.ratio_eval (F := F) y' β c d₀ hc' hd₀
    have hprod : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) = (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) *
        (aeval y (ResidueGen.ratioMon (F := F) β c d₀) / aeval y (ResidueGen.ratioMon (F := F) β d₀ c)) := by
      rw [eqΩ]
      field_simp
    have hmem : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R := by
      rw [hprod]
      exact mul_mem h0R hrR
    refine ⟨hmem, ?_⟩
    have hsplit : (⟨_, hmem⟩ : R) = ⟨_, h0R⟩ * ⟨_, hrR⟩ := Subtype.ext hprod
    rw [hsplit, map_mul, hr, eqK, ext_eq _ h0R]
    ring
  refine ⟨fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)),
    fun h hH => key h hH d₀ hd₀, ?_⟩
  intro c hc'
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
  have hGc' : (∏ k, y' ⟨k, c k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc' k)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨h, hH, rfl⟩
    rw [SetLike.mem_coe, PowRealises.mem_span_inv_iff _ hGc']
    obtain ⟨hh, he⟩ := key h hH c hc'
    obtain ⟨_, hin⟩ := hchart c hc' _ ((PowRealises.mem_secOver y β h).mp hH c hc)
    beta_reduce
    rw [← he]
    exact hin
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hg⟩ := hgen
    obtain ⟨u, hu, hsum⟩ := hg c hc
    choose hUR hUc using fun j => hchart c hc' _ (hu j)
    choose hWR hW using fun j => key (s j) (hs j) c hc'
    have hsumR : (∑ j, (⟨u j, hUR j⟩ : R) * ⟨_, hWR j⟩) = 1 := by
      apply Subtype.ext
      push_cast
      exact hsum
    have hone := congrArg σ hsumR
    rw [map_sum, map_one] at hone
    have h2 : (∑ j, σ ⟨u j, hUR j⟩ *
        (ext (s j * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)))) *
          (∏ k, y' ⟨k, c k⟩ ^ (-β k)) = 1 := by
      rw [Finset.sum_mul, ← hone]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hW j]
      ring
    rw [← eq_inv_of_mul_eq_one_left h2]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hj := Submodule.smul_mem
      (Submodule.span (chartRingOver F y' c)
        ((fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k))) ''
          (secOver F y β : Set Ω)))
      (⟨_, hUc j⟩ : chartRingOver F y' c) (Submodule.subset_span (Set.mem_image_of_mem _ (hs j)))
    rwa [Subalgebra.smul_def, smul_eq_mul] at hj

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreCoordNeZeroIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

section Segre

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

def segreCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Ω := ∏ k, y ⟨k, c k⟩

omit [DecidableEq K] in

theorem segreCoord_ne_zero_iff (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    segreCoord y c ≠ 0 ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  unfold segreCoord
  rw [Finset.prod_ne_zero_iff]
  simp

theorem segreCoord_update_div (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    segreCoord y (Function.update c k i) / segreCoord y c = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
  unfold segreCoord
  rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]
  have hrest : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k i k'⟩ =
      ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have hne : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => hc k'
  simp only [Function.update_self]
  rw [hrest, mul_div_mul_right _ _ hne]

variable (R : Type) [CommRing R] [Algebra R Ω]

theorem chartRingOver_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    chartRingOver R y c = chartRingOver R (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (segreCoord y)) (fun _ => c) := by
  apply le_antisymm
  · unfold chartRingOver
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    have h := segreCoord_update_div y c hc k i
    simp only at h ⊢
    rw [← h]
    exact Algebra.subset_adjoin ⟨⟨(), Function.update c k i⟩, rfl⟩
  · conv_lhs => unfold chartRingOver
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨u, d⟩, rfl⟩
    show segreCoord y d / segreCoord y c ∈ chartRingOver R y c
    unfold segreCoord
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, d k⟩, rfl⟩

theorem sameModel_segreCoord (y : (Σ k, ι k) → Ω) :
    IndefiniteRowSideFullHecke.Kleiman2.SameModel R y (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (segreCoord y)) := by
  apply sameModel_of_charts
  · intro c hc
    refine ⟨fun _ => c, fun _ => (segreCoord_ne_zero_iff y c).mpr hc, chartRingOver_segre R y c hc⟩
  · intro c' hc'
    have hc : ∀ k, y ⟨k, c' () k⟩ ≠ 0 := (segreCoord_ne_zero_iff y (c' ())).mp (hc' ())
    exact ⟨c' (), hc, chartRingOver_segre R y (c' ()) hc⟩

end Segre

theorem SegreModel.full : SegreModel.Statement := by
  intro K _ _ ι _ _ Ω _ y hy
  classical
  choose c₀ hc₀ using hy
  have hpos : 0 < Fintype.card (∀ k, ι k) := Fintype.card_pos_iff.mpr ⟨c₀⟩
  let e : (∀ k, ι k) ≃ Fin (Fintype.card (∀ k, ι k) - 1 + 1) :=
    (Fintype.equivFin _).trans (finCongr (by omega))
  refine ⟨Fintype.card (∀ k, ι k) - 1, e, segreCoord y ∘ e.symm, fun c => by simp [segreCoord], ?_, ?_⟩
  · intro h0
    have h1 := congrFun h0 (e c₀)
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h1
    exact (segreCoord_ne_zero_iff y c₀).mpr hc₀ h1
  · intro R _ _
    exact (sameModel_segreCoord R y).trans (sameModel_reindex R (segreCoord y) e)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

