import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u w

theorem CutComponent.proof (hZ : CutZeroNotLe.Statement.{u, w}) (hE : CutNonempty.Statement.{u, w})
    (hD : CutDimLower.Statement.{u, w}) : CutComponent.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hI
  obtain ⟨qq, hq, j, hj⟩ := hE k Ω N x n pp L s hW hL hs hI
  obtain ⟨f, hfZ, hfp⟩ := hZ k Ω N x (n + 1) pp L s hW hs hI
  have hlo := hD k Ω N x n pp L s qq hW hs hq ⟨j, hj⟩
  have hJq : pp ⊔ zeroIdeal L.toSubSystem s ≤ qq := hq.1.2
  have hqp : qq.IsPrime := hq.1.1
  have hppq : pp ≤ qq := le_sup_left.trans hJq
  have := hW.isPrime

  have hpH : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    intro i r hr
    have := hW.homog r hr i
    rwa [← decomposition.decompose'_apply] at this
  have hZH : (zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ (by rintro f ⟨c, hc, -⟩; exact ⟨c, hc⟩)
  have hJH : (pp ⊔ zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    have h := (HomogeneousIdeal.toIdeal_sup ⟨pp, hpH⟩ ⟨_, hZH⟩).symm ▸
      (⟨pp, hpH⟩ ⊔ ⟨_, hZH⟩ : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous
    exact h

  have hcore : qq ≤ (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
    refine hq.2 ⟨hqp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    rw [← hJH.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJq
  have hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq := by
    intro p hp d
    have := (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous d (hcore hp)
    have h2 : homogeneousComponent d p ∈
        (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
      rw [← decomposition.decompose'_apply]
      exact this
    exact Ideal.toIdeal_homogeneousCore_le _ _ h2

  have hup : ringKrullDim (Poly k N ⧸ qq) + 1 ≤ ((n + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hW.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hppq)
      (Ideal.Quotient.factor_surjective hppq) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hJq (Ideal.mem_sup_right hfZ)
  refine ⟨qq, hq, hqp, hhom, hW.le.trans hppq, ⟨j, hj⟩, ?_⟩

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize ringKrullDim (Poly k N ⧸ qq) = D at hup hlo ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hlo (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe m =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have h1 : n + 1 ≤ m := by exact_mod_cast hlo
      have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have h3 := Nat.cast_le.mp h2
      have : m = n + 1 := by omega
      subst this
      rfl

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutZeroNotLeAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_zeroIdeal_div_eq (D : SubFamily S x Ω) (hfg : ∀ K, (D.sub K).FG) (I : Chart x)
    {σ y : Ω} (hσ : σ ∈ D.sub I) (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∃ (g t : Poly S N) (n : ℕ), g ∈ zeroIdeal D.toSubSystem σ ∧ t ∈ monos I.1 ∧
      g.IsHomogeneous n ∧ t.IsHomogeneous n ∧ σ * y = aeval x g / aeval x t := by
  classical

  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy σ hσ
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * σ * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  have hyU := mul_mem_chartRing_union D I
  choose G hG using hfg
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (D.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)

  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  have hUK : ∀ (K : Chart x), ∀ δ ∈ D.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ zeroIdeal D.toSubSystem σ := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]
      ring
  refine ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end CutZeroNotLeAux

theorem CutZeroNotLe.proof : CutZeroNotLe.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp L s _ hs ⟨I, hI⟩
  have hsI : s ∈ L.sub I := (Submodule.mem_iInf _).mp hs I
  obtain ⟨P, hP⟩ := L.invertible I

  have hex : ∃ y ∈ P, s * y ∉ idealMod pp I := by
    by_contra hcon
    push Not at hcon
    apply hI
    rw [SubSystem.twist_sub_eq_mul_sub]
    have hle : Submodule.span (chartRing k x I) {s} * P ≤ idealMod pp I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (hcon b hb)
    have hmem : s ∈ Submodule.span (chartRing k x I) {s} * P * L.sub I := by
      rw [mul_assoc, mul_comm P, hP, mul_one]
      exact Submodule.mem_span_singleton_self s
    exact mul_le_mul' hle le_rfl hmem
  obtain ⟨y, hyP, hsy⟩ := hex
  have hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := by
    intro δ hδ
    have h := Submodule.mul_mem_mul hδ hyP
    rw [hP] at h
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp h
    rw [mul_comm, ← ha]
    exact a.2
  obtain ⟨g, t, n, hg, ht, hgn, htn, hst⟩ := exists_zeroIdeal_div_eq L.toSubFamily L.fg I hsI hy
  refine ⟨g, hg, fun hgp => hsy ?_⟩
  rw [hst]
  exact Submodule.subset_span ⟨g, t, n, hgp, ht, hgn, htn, rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem interSum_one (pp : Ideal (Poly S N)) (L : SubSystem S x Ω) (c : ℕ) :
    interSum pp ![L] c = restrLen pp (L.twist (twistSys S x (c : ℤ))) -
      restrLen pp ((twistSys S x 0).twist (twistSys S x (c : ℤ))) := by
  have h0 : tensorSub ![L] ∅ = twistSys S x 0 := by simp [tensorSub]
  have h1 : tensorSub ![L] {0} = L := by
    simp [tensorSub, List.finRange_succ, twistSys_zero_twist]
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [interSum, huniv, Finset.sum_pair (by decide), h0, h1]
  simp only [Finset.card_empty, Finset.card_singleton]
  norm_num
  ring

theorem restrLen_of_irrelevant (pp : Ideal (Poly S N)) (hX : ∀ i, (X i : Poly S N) ∈ pp)
    (F : SubSystem S x Ω) : restrLen pp F = 0 := by
  have hle : F.secs ≤ (F.twist (idealSys x pp)).secs := by
    intro y hy
    simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hX i, X_mem_monos hi, isHomogeneous_X S i,
        isHomogeneous_X S i, by rw [aeval_X, div_self hxi]⟩
    exact Submodule.subset_span ⟨1, h1, y, hy I, (one_smul Ω y).symm⟩
  have hs : Subsingleton (F.secs ⧸ ((F.twist (idealSys x pp)).secs).comap F.secs.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    intro y _
    exact hle y.2
  unfold restrLen
  rw [Module.length_eq_zero_iff.mpr hs]
  rfl

theorem ringKrullDim_quot_succ_le {G pp : Ideal (Poly S N)} [G.IsPrime] (hle : G ≤ pp) {f : Poly S N}
    (hfp : f ∈ pp) (hfG : f ∉ G) : ringKrullDim (Poly S N ⧸ pp) + 1 ≤ ringKrullDim (Poly S N ⧸ G) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
  · apply mem_nonZeroDivisors_of_ne_zero
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfp

theorem withBot_le_one_of_le_two {a : WithBot ℕ∞} (h2 : a ≤ 2)
    (hne : a ≠ ((1 + 1 : ℕ) : WithBot ℕ∞)) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h2 (by decide)
    | coe n =>
      have h2a : (n : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp h2
      have h2' : n ≤ 2 := by exact_mod_cast h2a
      have hne' : n ≠ 2 := fun h => hne (by rw [h]; rfl)
      have h1 : (n : ℕ∞) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
      exact WithBot.coe_le_coe.mpr h1

theorem withBot_not_succ_le {a b : WithBot ℕ∞} (ha : a = ((1 + 1 : ℕ) : WithBot ℕ∞)) (hab : a + 1 ≤ b)
    (hb : b ≤ 2) : False := by
  subst ha
  have := hab.trans hb
  exact absurd this (by decide)

end Lemmas

open Classical in

theorem CycleSplit.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hCu : CycleSplit.Curve.Statement.{u, w})
    (hSm : CycleSplit.Small.Statement.{u, w}) : CycleSplit.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M 𝔪 h𝔪 J hJhom hJle hJm hdim
  obtain ⟨n, pp, d, hpp, hcount, hres⟩ := hF S Ω N x 𝔪 h𝔪 J hJhom hJle hJm

  let v : Ideal (Poly S N) → ℤ := fun G => if IsSubvar x G 1 then interNum G ![M.toSubSystem] else 0

  have hdimj : ∀ j, ringKrullDim (Poly S N ⧸ pp j) ≤ 2 := by
    intro j
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hGle)
      (Ideal.Quotient.factor_surjective hGle)).trans (hdim G hG)

  have hmin : ∀ j, IsSubvar x (pp j) 1 → pp j ∈ J.minimalPrimes := by
    intro j hsv
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    by_cases hGe : G = pp j
    · rw [← hGe]; exact hG
    · exfalso
      have : G.IsPrime := hG.1.1
      obtain ⟨f, hfp, hfG⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hGle hGe)
      exact withBot_not_succ_le hsv.dim (ringKrullDim_quot_succ_le hGle hfp hfG) (hdim G hG)

  have hpiece : ∀ j, ∀ᶠ c : ℕ in atTop, interSum (pp j) ![M.toSubSystem] c = v (pp j) := by
    intro j
    obtain ⟨hjp, hjh, hJj⟩ := hpp j
    by_cases hsv : IsSubvar x (pp j) 1
    · simp only [v, if_pos hsv]
      exact hCu S Ω N x M 𝔪 h𝔪 (pp j) hsv (hJm.trans hJj)
    · simp only [v, if_neg hsv]
      by_cases hrel : ∃ i, (X i : Poly S N) ∉ pp j
      · refine hSm S Ω N x M 𝔪 h𝔪 (pp j) hjp hjh (hJle.trans hJj) (hJm.trans hJj) ?_
        exact withBot_le_one_of_le_two (hdimj j) fun h => hsv ⟨hjp, hjh, hJle.trans hJj, hrel, h⟩
      · push Not at hrel
        exact Eventually.of_forall fun c => by
          rw [interSum_one, restrLen_of_irrelevant _ hrel, restrLen_of_irrelevant _ hrel, sub_zero]

  have hshift : ∀ j, ∀ᶠ c : ℕ in atTop,
      0 ≤ (c : ℤ) + d j ∧ interSum (pp j) ![M.toSubSystem] ((c : ℤ) + d j).toNat = v (pp j) := by
    intro j
    have ht : Tendsto (fun c : ℕ => ((c : ℤ) + d j).toNat) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun b => ⟨b + (d j).natAbs, fun a ha => ?_⟩
      omega
    exact ((eventually_ge_atTop (d j).natAbs).and (ht.eventually (hpiece j))).mono
      fun c hc => ⟨by omega, hc.2⟩
  have hall := Filter.eventually_all.mpr hshift
  filter_upwards [hall, hres M, hres (twistBundle S x 0)] with c hc hM h0
  have h0' : restrLen J ((twistSys S x 0).twist (twistSys S x (c : ℤ))) =
      ∑ j, restrLen (pp j) ((twistSys S x 0).twist (twistSys S x ((c : ℤ) + d j))) := h0

  have hsum : interSum J ![M.toSubSystem] c = ∑ j, v (pp j) := by
    rw [interSum_one, hM, h0', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← (hc j).2, interSum_one, Int.toNat_of_nonneg (hc j).1]
  rw [hsum, Finset.sum_comp (fun G => v G) pp]

  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image pp) ?_]
  · refine Finset.sum_congr rfl fun G hG => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hG
    by_cases hsv : IsSubvar x (pp j) 1
    · have hm := hmin j hsv
      have : (pp j).IsPrime := (hpp j).1
      rw [dif_pos ⟨hm, hsv⟩, nsmul_eq_mul]
      simp only [v, if_pos hsv]
      rw [← hcount (pp j) hm, ENat.toNat_natCast]
    · rw [dif_neg fun h => hsv h.2]
      simp only [v, if_neg hsv, smul_zero]
  · intro G hG
    rw [Function.mem_support] at hG
    split_ifs at hG with h
    · have : G.IsPrime := h.1.1.1
      have hc0 : (cutMult J G).toNat ≠ 0 := by
        intro h0; rw [h0] at hG; simp at hG
      rw [← hcount G h.1, ENat.toNat_natCast] at hc0
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
      rw [Finset.mem_filter] at hj
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨j, hj.2⟩
    · exact absurd rfl hG

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeBadFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

theorem KHFreeBadFinite.full : KHFreeBadFinite.Statement := by
  intro K _ ι _ e
  refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Icc (-|e p.1|) |e p.1|)
    (fun p => Set.finite_Icc _ _)).subset ?_
  rintro a ⟨hsum, hneg⟩ ⟨k, i⟩ -
  show a ⟨k, i⟩ ∈ Set.Icc (-|e k|) |e k|
  rw [Set.mem_Icc, ← abs_le]
  have hs : ∑ j, a ⟨k, j⟩ = e k := congrFun hsum k
  rcases hneg k with h | h
  · have hnn : ∀ j, 0 ≤ a ⟨k, j⟩ := by
      intro j
      by_contra hj
      have hj2 : a ⟨k, j⟩ < 0 := lt_of_not_ge hj
      have hj' : j ∈ negSet a k := by simp [negSet, hj2]
      rw [h] at hj'
      simp at hj'
    have h1 : a ⟨k, i⟩ ≤ ∑ j, a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => a ⟨k, j⟩) (fun j _ => hnn j) (Finset.mem_univ i)
    rw [abs_of_nonneg (hnn i)]
    linarith [le_abs_self (e k)]
  · have hng : ∀ j, a ⟨k, j⟩ < 0 := by
      intro j
      have hj : j ∈ negSet a k := by rw [h]; exact Finset.mem_univ j
      simpa [negSet] using hj
    have h1 : -a ⟨k, i⟩ ≤ ∑ j, -a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => -a ⟨k, j⟩) (fun j _ => by linarith [hng j])
        (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib] at h1
    rw [abs_of_neg (hng i)]
    linarith [neg_abs_le (e k)]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotDevissage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [Module S E] [IsScalarTower S Ω E] in

theorem twist_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) (Q : SubSystem S x Ω)
    (I : Chart x) : (F.twist Q).sub I ≤ (G.twist Q).sub I :=
  Submodule.span_mono fun _ ⟨q, hq, y, hy, hz⟩ => ⟨q, hq, y, h I hy, hz⟩

omit [Module S E] [IsScalarTower S Ω E] in

theorem twistPows_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ) (I : Chart x),
      (F.twistPows t L n).sub I ≤ (G.twistPows t L n).sub I
  | 0, _, _, I => h I
  | t + 1, _, _, I => twist_sub_mono (twistPows_sub_mono h t _ _) _ I

theorem exists_subFamily_twistPows (hB : SubFamilyTwist.Statement.{u, v, w}) (F : SubFamily S x E)
    (hF : ∀ I, (F.sub I).FG) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      ∃ H : SubFamily S x E, H.toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n ∧
        ∀ I, (H.sub I).FG
  | 0, _, _ => ⟨F, rfl, hF⟩
  | t + 1, L, n => by
    obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB F hF t (fun j => L j.castSucc) (fun j => n j.castSucc)
    obtain ⟨P, hP⟩ := exists_lineBundle_twistMul (L (Fin.last t)) (n (Fin.last t)) 0
    obtain ⟨G, hG, hGfg⟩ := hB S Ω N x E H P hHfg
    refine ⟨G, ?_, hGfg⟩
    rw [hG, hP, hH, twistMul, SubSystem.twist_twistSys_zero]
    rfl

end Lemmas

theorem SnapperQuotDevissage.proof (hF : SnapperQuotFilt.Statement.{u, v, w})
    (hI : SnapperQuotIso.Statement.{u, v, w, w}) (hA : SnapperQuotAdd.Statement.{u, v, w})
    (hB : SubFamilyTwist.Statement.{u, v, w}) : SnapperQuotDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  obtain ⟨r, G, pp, a, hGfg, hG0, hGr, hmono, hpp, hiso⟩ := hF k Ω N x E F₁ F₂ hfg hle J hJ hxJ hJF
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  have hH : ∀ m, ∃ H : SubFamily k x E, H.toSubSystem =
      ((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) ∧
        ∀ I, (H.sub I).FG := fun m => by
    obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB (G m) (hGfg m) t L n
    obtain ⟨H', hH', hH'fg⟩ := hB k Ω N x E H (twistBundle k x c) hHfg
    exact ⟨H', by rw [hH', hH]; rfl, hH'fg⟩
  choose H hHeq hHfg using hH
  have hHmono : ∀ m < r, ∀ I, (H m).sub I ≤ (H (m + 1)).sub I := fun m hm I => by
    rw [hHeq, hHeq]
    exact twist_sub_mono (twistPows_sub_mono (hmono m hm) t _ n) _ I
  have hstep : ∀ m (hm : m < r), eulerCharQuot k (H (m + 1)).toSubSystem (H m).toSubSystem =
      pieceChar k (pp ⟨m, hm⟩) (a ⟨m, hm⟩) L n c := fun m hm => by
    rw [hHeq, hHeq]
    exact hI k Ω N x E Ω _ _ _ _ (hiso ⟨m, hm⟩ t L n c).some
  have key : ∀ m ≤ r, (∀ I, (H 0).sub I ≤ (H m).sub I) ∧
      eulerCharQuot k (H m).toSubSystem (H 0).toSubSystem =
        ∑ i ∈ Finset.range m, (if h : i < r then pieceChar k (pp ⟨i, h⟩) (a ⟨i, h⟩) L n c else 0) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨fun I => le_rfl, by simp [eulerCharQuot_self]⟩
    | succ m ih =>
      intro hm
      obtain ⟨h0, hχ⟩ := ih (by omega)
      refine ⟨fun I => (h0 I).trans (hHmono m (by omega) I), ?_⟩
      rw [hA k Ω N x E (H (m + 1)) (H m) (H 0) (hHfg _) (hHmono m (by omega)) h0, hχ,
        hstep m (by omega), Finset.sum_range_succ, dif_pos (by omega), add_comm]
  rw [← hGr, ← hG0, ← hHeq r, ← hHeq 0, (key r le_rfl).2, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp [i.2]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

