import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0044

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIntegrallyClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

namespace NormalGermIntegrallyClosed

theorem analyticAt_of_differentiableOn {σ : Type} [Fintype σ] {N : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}
    (hN : IsOpen N) (hf : DifferentiableOn ℂ f N) {z : σ → ℂ} (hz : z ∈ N) : AnalyticAt ℂ f z := by
  let L : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
  have hO : IsOpen (L ⁻¹' N) := hN.preimage L.continuous
  have hg : DifferentiableOn ℂ (f ∘ L) (L ⁻¹' N) :=
    hf.comp L.differentiable.differentiableOn fun x hx => hx
  have hA : AnalyticOnNhd ℂ (f ∘ L) (L ⁻¹' N) := by
    refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun x hx i => ?_
    have h1 : DifferentiableAt ℂ (f ∘ L) (Function.update x i (x i)) := by
      rw [Function.update_eq_self]
      exact hg.differentiableAt (hO.mem_nhds hx)
    exact h1.comp (x i) (hasFDerivAt_update x (x i)).differentiableAt
  have hz' : L.symm z ∈ L ⁻¹' N := by simpa using hz
  have h2 := (hA _ hz').comp ((L.symm : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)).analyticAt z)
  simpa [Function.comp_def] using h2

def anFun {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' := fun hf => hf.neg

def toGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : anFun w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (anFun w).subtype).codRestrict (holGerms w) fun u => ⟨u.1, u.2, rfl⟩

theorem toGerm_surjective {σ : Type} [Fintype σ] (w : σ → ℂ) : Function.Surjective (toGerm w) := by
  rintro ⟨φ, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem toGerm_eq_iff {σ : Type} [Fintype σ] {w : σ → ℂ} {u v : anFun w} :
    toGerm w u = toGerm w v ↔ (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem vanish_of_mem_map {σ : Type} [Fintype σ] {I : Ideal (MvPolynomial σ ℂ)} {w : σ → ℂ} {u : anFun w}
    (hu : toGerm w u ∈ I.map (polyGerm w)) :
    ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 := by
  have key : ∀ x, x ∈ Submodule.span (holGerms w) (polyGerm w '' (I : Set (MvPolynomial σ ℂ))) →
      ∃ v : anFun w, toGerm w v = x ∧ ∀ᶠ z in 𝓝[zeroSetIn I] w, (v : (σ → ℂ) → ℂ) z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩, rfl,
        eventually_nhdsWithin_of_forall fun z hz => hz q hq⟩
    | zero => exact ⟨0, map_zero _, Eventually.of_forall fun z => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, rfl, hu⟩ := hx
      obtain ⟨v, rfl, hv⟩ := hy
      exact ⟨u + v, map_add _ _ _, by filter_upwards [hu, hv] with z h1 h2; simp [h1, h2]⟩
    | smul c x _ hx =>
      obtain ⟨v, rfl, hv⟩ := hx
      obtain ⟨b, rfl⟩ := toGerm_surjective w c
      exact ⟨b * v, by rw [map_mul, smul_eq_mul], by filter_upwards [hv] with z h; simp [h]⟩
  obtain ⟨v, hv, hv0⟩ := key _ hu
  have he : (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := toGerm_eq_iff.1 hv.symm
  filter_upwards [nhdsWithin_le_nhds he, hv0] with z h1 h2
  rw [h1, h2]

theorem exists_eq_mul_of_integral_relation {S : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    {d : ℕ} (f g : S) (a : Fin d → S) (hg : g ≠ 0)
    (hrel : f ^ d + ∑ j, a j * f ^ (j : ℕ) * g ^ (d - (j : ℕ)) = 0) : ∃ y, f = g * y := by
  let K := FractionRing S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  have hrelK : algebraMap S K f ^ d + ∑ j, algebraMap S K (a j) * algebraMap S K f ^ (j : ℕ) *
      algebraMap S K g ^ (d - (j : ℕ)) = 0 := by
    have h2 := congrArg (algebraMap S K) hrel
    simp only [map_add, map_sum, map_mul, map_pow, map_zero] at h2
    exact h2
  have hg0 : algebraMap S K g ≠ 0 := fun h0 => hg (hinj (by rw [h0, map_zero]))
  generalize hfK : algebraMap S K f = fK at hrelK
  generalize hgK : algebraMap S K g = gK at hrelK hg0
  have hint : IsIntegral S (fK / gK) := by
    refine ⟨Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
    have hterm : ∀ j : Fin d, algebraMap S K (a j) * (fK / gK) ^ (j : ℕ) =
        algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) / gK ^ d := by
      intro j
      rw [eq_div_iff (pow_ne_zero _ hg0), div_pow,
        show gK ^ d = gK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) by rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
      have hj : gK ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hg0
      rw [show algebraMap S K (a j) * (fK ^ (j : ℕ) / gK ^ (j : ℕ)) * (gK ^ (j : ℕ) * gK ^ (d - (j : ℕ))) =
          algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) * (gK ^ (j : ℕ) / gK ^ (j : ℕ)) by ring,
        div_self hj, mul_one]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [Finset.sum_congr rfl fun j _ => hterm j, div_pow, ← Finset.sum_div, ← add_div, hrelK, zero_div]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hfK, hgK, mul_div_assoc', eq_div_iff hg0, mul_comm]

theorem proof (hRueckert : RueckertNullstellensatz.Statement)
    (hZariski : ZariskiAnalyticNormality.Statement) : NormalGermIntegrallyClosed.Statement := by
  intro σ _ I w N F G d a hI hIc hw hN hwN hF hG ha hGnz hrel
  have hFa : AnalyticAt ℂ F w := analyticAt_of_differentiableOn hN hF hwN
  have hGa : AnalyticAt ℂ G w := analyticAt_of_differentiableOn hN hG hwN
  have haa : ∀ j, AnalyticAt ℂ (a j) w := fun j => analyticAt_of_differentiableOn hN (ha j) hwN

  obtain ⟨k, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hpI : ∀ i, p i ∈ I := fun i => hp ▸ Submodule.subset_span ⟨i, rfl⟩
  have hZp : ∀ z, (∀ i, eval z (p i) = 0) → z ∈ zeroSetIn I := by
    intro z hz q hq
    have hle : I ≤ RingHom.ker (eval z) := by
      rw [← hp]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
    exact RingHom.mem_ker.1 (hle hq)

  obtain ⟨hJ, hJc⟩ := hZariski σ I w hI hIc hw
  let J := I.map (polyGerm w)
  have : J.IsPrime := hJ
  let S := holGerms w ⧸ J
  have : IsIntegrallyClosed S := hJc
  let π : anFun w →+* S := (Ideal.Quotient.mk J).comp (toGerm w)
  have hπ0 : ∀ u : anFun w, π u = 0 → ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 :=
    fun u hu => vanish_of_mem_map (Ideal.Quotient.eq_zero_iff_mem.1 hu)
  have hπpoly : ∀ q ∈ I, π ⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩ = 0 := fun q hq =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hq)
  have hπeq : ∀ u v : anFun w, (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v → π u = π v := fun u v h => by
    simp only [π, RingHom.comp_apply, toGerm_eq_iff.2 h]

  let FA : anFun w := ⟨F, hFa⟩
  let GA : anFun w := ⟨G, hGa⟩
  let aA : Fin d → anFun w := fun j => ⟨a j, haa j⟩
  let PA : anFun w := FA ^ d + ∑ j, aA j * FA ^ (j : ℕ) * GA ^ (d - (j : ℕ))
  have hPA : ∀ z, (PA : (σ → ℂ) → ℂ) z =
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) := by
    intro z
    simp [PA, FA, GA, aA, Finset.sum_apply]

  have hGS : π GA ≠ 0 := by
    intro h
    exact hGnz (eventually_nhdsWithin_iff.1 (hπ0 GA h))

  have hvan : ∀ᶠ z in 𝓝 w, (∀ i, eval z (p i) = 0) → (PA : (σ → ℂ) → ℂ) z * G z = 0 := by
    filter_upwards [hN.mem_nhds hwN] with z hzN hz
    by_cases hG0 : G z = 0
    · rw [hG0, mul_zero]
    · rw [hPA, hrel z ⟨⟨hZp z hz, hzN⟩, hG0⟩, zero_mul]
  obtain ⟨m, h, hm, hh, hgm⟩ := hRueckert σ w k (fun i z => eval z (p i))
    (fun z => (PA : (σ → ℂ) → ℂ) z * G z) (fun i => analyticAt_eval_polynomial w (p i))
    (PA.2.mul hGa) hvan
  let hA : Fin k → anFun w := fun i => ⟨h i, hh i⟩
  let pA : Fin k → anFun w := fun i => ⟨fun z => eval z (p i), analyticAt_eval_polynomial w (p i)⟩
  have hprod : π ((PA * GA) ^ m) = π (∑ i, hA i * pA i) := by
    apply hπeq
    filter_upwards [hgm] with z hz
    simpa [hA, pA, GA, Finset.sum_apply, mul_pow] using hz
  have hPS : π PA = 0 := by
    have h1 : (π PA * π GA) ^ m = 0 := by
      rw [← map_mul, ← map_pow, hprod, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hπpoly _ (hpI i), mul_zero]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 hm)).1 h1)).resolve_right hGS

  have : IsDomain S := Ideal.Quotient.isDomain J
  obtain ⟨y, hy⟩ := exists_eq_mul_of_integral_relation (π FA) (π GA) (fun j => π (aA j)) hGS (by
    rw [← hPS]
    simp only [PA, map_add, map_sum, map_mul, map_pow])
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨HA, rfl⟩ := toGerm_surjective w φ
  have hdiff : π (FA - GA * HA) = 0 := by
    rw [map_sub, map_mul, hy]
    exact sub_self _
  have hv := eventually_nhdsWithin_iff.1 (hπ0 _ hdiff)
  obtain ⟨V, hV, hVo, hwV⟩ := eventually_nhds_iff.1 (hv.and HA.2.eventually_analyticAt)
  refine ⟨V, hVo, hwV, HA, fun z hz => (hV z hz).2.differentiableAt.differentiableWithinAt, ?_⟩
  rintro z ⟨hzZ, hzV⟩
  have h3 := (hV z hzV).1 hzZ
  change F z - G z * (HA : (σ → ℂ) → ℂ) z = 0 at h3
  exact sub_eq_zero.1 h3

end NormalGermIntegrallyClosed

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalZerosNowhereDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isAnalyticNear_zeroSetIn {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨Set.univ, s.card, fun i z => eval z (s.equivFin.symm i : MvPolynomial σ ℂ), isOpen_univ, trivial,
    fun i => AnalyticOnNhd.eval_mvPolynomial _, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, true_and]
  constructor
  · intro hz i
    apply hz
    rw [← hs]
    exact Submodule.subset_span (s.equivFin.symm i).2
  · intro hz q hq
    have hle : Ideal.span (s : Set (MvPolynomial σ ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [Ideal.span_le]
      intro p hp
      rw [SetLike.mem_coe, RingHom.mem_ker]
      simpa using hz (s.equivFin ⟨p, hp⟩)
    rw [← hs] at hq
    exact hle hq

theorem analyticOnNhd_of_differentiableOn_scalar_fin {d : ℕ} {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : AnalyticOnNhd ℂ F U := by
  refine analyticOnNhd_of_continuousOn_of_separately hU hF.continuousOn (fun z hz i => ?_)
  have h1 : DifferentiableAt ℂ F (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hF.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem germIrreducibleAt_zeroSetIn_of_integrallyClosed (hic : NormalGermIntegrallyClosed.Statement)
    {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (hI : I.IsPrime)
    (hn : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I)) (hw : w ∈ zeroSetIn I) :
    GermIrreducibleAt (zeroSetIn I) w := by
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfne, hgne⟩ := hcon
  set X := zeroSetIn I with hX
  set N : Set (σ → ℂ) :=
    ({z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z}) ∩ interior {z | z ∈ X → f z * g z = 0} with hNdef
  have hNo : IsOpen N := ((isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)).inter isOpen_interior
  have hwN : w ∈ N := ⟨⟨hf, hg⟩, mem_interior_iff_mem_nhds.mpr hfg⟩
  have hfd : DifferentiableOn ℂ f N := fun z hz => hz.1.1.differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℂ g N := fun z hz => hz.1.2.differentiableAt.differentiableWithinAt
  have hfgN : ∀ z ∈ X ∩ N, f z * g z = 0 := fun z hz => interior_subset hz.2.2 hz.1
  have hGne : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → (f + g) z = 0 := by
    intro hev
    apply hfne
    filter_upwards [hev, hfg] with z h1 h2 hz
    have hs : f z + g z = 0 := h1 hz
    have hp : f z * g z = 0 := h2 hz
    have hff : f z * f z = 0 := by linear_combination f z * hs - hp
    exact mul_self_eq_zero.mp hff
  have ha : ∀ j, DifferentiableOn ℂ ((![0, -1] : Fin 2 → (σ → ℂ) → ℂ) j) N := by
    intro j
    fin_cases j
    · exact differentiableOn_const (0 : ℂ)
    · exact differentiableOn_const (-1 : ℂ)
  obtain ⟨V, hV, hwV, H, hH, hfH⟩ := hic σ I w N f (f + g) 2 ![0, -1] hI hn hw hNo hwN hfd (hfd.add hgd)
    ha hGne (by
      intro z hz
      have hp := hfgN z hz.1
      simp [Fin.sum_univ_two]
      linear_combination -hp)
  have hHc : ContinuousAt H w := (hH.differentiableAt (hV.mem_nhds hwV)).continuousAt
  have hev : ∀ᶠ z in 𝓝 w, z ∈ V ∧ (z ∈ X → f z * g z = 0) := (show ∀ᶠ z in 𝓝 w, z ∈ V from hV.mem_nhds hwV).and hfg
  rw [Filter.not_eventually] at hfne hgne
  have h1 : H w = 1 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hfne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hg0 : g z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_left hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hg0, add_zero] at hfz
    exact hzH.2 (mul_left_cancel₀ hz.2 (hfz.symm.trans (mul_one _).symm))
  have h0 : H w = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hgne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hf0 : f z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_right hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hf0, zero_add] at hfz
    exact hzH.2 ((mul_eq_zero.mp hfz.symm).resolve_left hz.2)
  exact one_ne_zero (h1.symm.trans h0)

theorem NormalZerosNowhereDense.proof (hic : NormalGermIntegrallyClosed.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement) (hdense : RegularLocusDense.Statement) :
    NormalZerosNowhereDense.Statement := by
  intro σ _ I w N G hI hn hw hN hwN hG hne
  have han := isAnalyticNear_zeroSetIn I w
  have hirr := germIrreducibleAt_zeroSetIn_of_integrallyClosed hic I w hI hn hw
  set X := zeroSetIn I with hX
  obtain ⟨N₀, hN₀, hwN₀, hd⟩ := hdense σ X w han
  obtain ⟨B, hB, hwB, hBU, hpc⟩ :=
    hconn σ X w han hirr (N ∩ N₀) (Filter.inter_mem (hN.mem_nhds hwN) (hN₀.mem_nhds hwN₀))
  have hBN : B ⊆ N := hBU.trans Set.inter_subset_left
  have hdB : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hd B hB (hBU.trans Set.inter_subset_right)
  refine ⟨B, hB, hwB, hBN, ?_⟩
  intro z hz V hV
  by_contra hall
  push Not at hall
  set R := regLocus (X ∩ B) with hR
  set T : Set (σ → ℂ) := {y | y ∈ X → G y = 0} with hT

  have hloc : ∀ x ∈ R, ∃ M : Set (σ → ℂ), IsOpen M ∧ x ∈ M ∧ ((∃ p ∈ X ∩ M, T ∈ 𝓝 p) → M ⊆ T) := by
    intro x hx
    have hx' : IsRegularPointOf (X ∩ B) x := hx
    obtain ⟨hxXB, d, A, O, W, g, hO, hW, hxW, hg, hAg, hYW⟩ := hx'
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := by rw [← hYW]; exact ⟨hxXB, hxW⟩
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y₀ hy₀O
    have hgO : ∀ y ∈ O, g y ∈ X ∩ B := by
      intro y hy
      have hy' : g y ∈ (X ∩ B) ∩ W := by rw [hYW]; exact Set.mem_image_of_mem g hy
      exact hy'.1
    have hxA : A x ∈ Metric.ball y₀ r := by
      rw [← hgy₀, hAg y₀ hy₀O]
      exact Metric.mem_ball_self hr
    refine ⟨W ∩ B ∩ A ⁻¹' Metric.ball y₀ r,
      (hW.inter hB).inter (Metric.isOpen_ball.preimage A.continuous), ⟨⟨hxW, hxXB.2⟩, hxA⟩, ?_⟩
    have hcov : ∀ p ∈ X ∩ (W ∩ B ∩ A ⁻¹' Metric.ball y₀ r), ∃ y ∈ Metric.ball y₀ r, g y = p := by
      rintro p ⟨hpX, ⟨hpW, hpB⟩, hpA⟩
      obtain ⟨y, hyO, rfl⟩ : p ∈ g '' O := by rw [← hYW]; exact ⟨⟨hpX, hpB⟩, hpW⟩
      refine ⟨y, ?_, rfl⟩
      have hpA' : A (g y) ∈ Metric.ball y₀ r := hpA
      rwa [hAg y hyO] at hpA'
    have hF : AnalyticOnNhd ℂ (fun y => G (g y)) (Metric.ball y₀ r) := by
      refine analyticOnNhd_of_differentiableOn_scalar_fin Metric.isOpen_ball (fun y hy => ?_)
      have hyO := hrO hy
      exact ((hG.differentiableAt (hN.mem_nhds (hBN (hgO y hyO).2))).comp y
        (hg y hyO).differentiableAt).differentiableWithinAt
    rintro ⟨p, hpXM, hpT⟩
    obtain ⟨y₁, hy₁, rfl⟩ := hcov p hpXM
    have hev : (fun y => G (g y)) =ᶠ[𝓝 y₁] 0 := by
      filter_upwards [(hg y₁ (hrO hy₁)).continuousAt.preimage_mem_nhds hpT,
        Metric.isOpen_ball.mem_nhds hy₁] with y hyT hyb
      exact hyT (hgO y (hrO hyb)).1
    have hzero := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y₀ r).isPreconnected hy₁ hev
    intro q hq hqX
    obtain ⟨y, hy, rfl⟩ := hcov q ⟨hqX, hq⟩
    exact hzero hy
  choose! M hMo hxM hMT using hloc

  have hallR : ∀ x ∈ R, T ∈ 𝓝 x := by
    obtain ⟨x₀, hx₀V, hx₀R⟩ := mem_closure_iff_nhds.mp (hdB hz) (interior V) (interior_mem_nhds.mpr hV)
    have hx₀T : T ∈ 𝓝 x₀ :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hx₀V) (fun y hy hyX => hall y ⟨hyX, interior_subset hy⟩)
    by_contra hbad
    push Not at hbad
    obtain ⟨x₁, hx₁R, hx₁T⟩ := hbad
    have hu : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hv : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hcover : R ⊆ (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) ∪ (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := by
      intro x hx
      by_cases h : T ∈ 𝓝 x
      · exact Or.inl (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
      · exact Or.inr (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
    obtain ⟨q, hqR, hqu, hqv⟩ := hpc _ _ hu hv hcover
      ⟨x₀, hx₀R, Set.mem_biUnion (x := x₀) ⟨hx₀R, hx₀T⟩ (hxM x₀ hx₀R)⟩
      ⟨x₁, hx₁R, Set.mem_biUnion (x := x₁) ⟨hx₁R, hx₁T⟩ (hxM x₁ hx₁R)⟩
    obtain ⟨a, ⟨haR, haT⟩, hqa⟩ := Set.mem_iUnion₂.mp hqu
    obtain ⟨b, ⟨hbR, hbT⟩, hqb⟩ := Set.mem_iUnion₂.mp hqv
    have hqX : q ∈ X := (regLocus_subset _ hqR).1
    have hMa : M a ⊆ T := hMT a haR ⟨a, ⟨(regLocus_subset _ haR).1, hxM a haR⟩, haT⟩
    have hqT : T ∈ 𝓝 q := Filter.mem_of_superset ((hMo a haR).mem_nhds hqa) hMa
    have hMb : M b ⊆ T := hMT b hbR ⟨q, ⟨hqX, hqb⟩, hqT⟩
    exact hbT (Filter.mem_of_superset ((hMo b hbR).mem_nhds (hxM b hbR)) hMb)

  have hzeroB : ∀ y ∈ X ∩ B, G y = 0 := by
    intro y hy
    by_contra hGy
    have hc : ContinuousAt G y := (hG.differentiableAt (hN.mem_nhds (hBN hy.2))).continuousAt
    obtain ⟨x, hxG, hxR⟩ := mem_closure_iff_nhds.mp (hdB hy) _ (hc.eventually_ne hGy)
    exact hxG (mem_of_mem_nhds (hallR x hxR) (regLocus_subset _ hxR).1)
  exact hne (Filter.mem_of_superset (hB.mem_nhds hwB) fun y hyB hyX => hzeroB y ⟨hyX, hyB⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionLocalCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionLocalCover.proof (hR : ProperOpenProjectionLocalUnbranched.Statement) :
    ProperOpenProjectionLocalCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨U₁, g, hU₁o, hy₀U₁, hU₁D, hg, hgd, hsec⟩ :=
    hR σ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU₁o y₀ hy₀U₁
  set U := Metric.ball y₀ r with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball
  have hy₀U : y₀ ∈ U := Metric.mem_ball_self hr
  have hUD : U ⊆ D := hball.trans hU₁D
  have hgU : AnalyticOnNhd ℂ g U := hg.mono hball
  have hgdU : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0 :=
    fun W hW hWU hWne => hgd W hW (hWU.trans hball) hWne

  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ A x ∈ U} with hYdef
  have hfib : ∀ y ∈ U, {x | x ∈ Y ∧ A x = y} = {x | x ∈ X ∩ B ∧ A x = y} := by
    intro y hy
    ext x
    simp only [hYdef, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx, _⟩, hAx⟩
      exact ⟨hx, hAx⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨⟨hx, hAx ▸ hy⟩, hAx⟩
  have hYmaps : Set.MapsTo A Y U := fun x hx => hx.2
  have hYprop : ∀ K ⊆ U, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKU hK
    have : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ B ∧ A x ∈ K} := by
      ext x
      simp only [hYdef, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKU h.2⟩, h.2⟩⟩
    rw [this]
    exact hprop K (hKU.trans hUD) hK
  have hYsec : ∀ x ∈ Y, g (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O := by
    intro x hx hgx
    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hXV⟩ := hsec (A x) (hball hx.2) hgx x hx.1 rfl
    refine ⟨O ∩ U, V ∩ A ⁻¹' U, h, hO.inter hUo, hV.inter (hUo.preimage A.continuous), ⟨hxV, hx.2⟩,
      hh.continuousOn.mono Set.inter_subset_left, fun y hy => hAh y hy.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨hzXB, hzU⟩, hzV, -⟩
      have : z ∈ h '' O := hXV ▸ ⟨hzXB, hzV⟩
      obtain ⟨y, hyO, rfl⟩ := this
      exact ⟨y, ⟨hyO, by rwa [hAh y hyO] at hzU⟩, rfl⟩
    · rintro ⟨y, ⟨hyO, hyU⟩, rfl⟩
      have hmem : h y ∈ X ∩ B ∩ V := hXV ▸ ⟨y, hyO, rfl⟩
      have hAy : A (h y) ∈ U := by rw [hAh y hyO]; exact hyU
      exact ⟨⟨hmem.1, hAy⟩, hmem.2, hAy⟩

  obtain ⟨n, hn⟩ := UnbranchedProperCountConstant.proof UnbranchedProperCountLocallyConstant.proof
    ManifoldZerosComplementConnected.proof σ Y d A U g hUo (convex_ball y₀ r).isPreconnected hYmaps hYprop
    hgU hYsec
  have hcount : ∀ y ∈ U, g y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = n := by
    intro y hy hgy
    rw [← hfib y hy]
    exact hn y hy hgy

  have hle : ∀ y ∈ U, {x | x ∈ X ∩ B ∧ A x = y}.encard ≤ n := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    have hn1 : ((n + 1 : ℕ) : ℕ∞) ≤ {x | x ∈ X ∩ B ∧ A x = y}.encard := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt hlt
    obtain ⟨T, hTF, hTcard⟩ := Set.exists_subset_encard_eq hn1
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
    obtain ⟨S, hS, hSdisj⟩ := hTfin.t2_separation
    have hW : U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x) ∈ 𝓝 y := by
      refine Filter.inter_mem (hUo.mem_nhds hy) ((Filter.biInter_mem hTfin).2 fun x hx => ?_)
      have hxF := hTF hx
      have := hopen x hxF.1 (S x) ((hS x).2.mem_nhds (hS x).1)
      rwa [hxF.2] at this
    obtain ⟨t, ⟨htW, hgt⟩⟩ := hgdU (interior (U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x))) isOpen_interior
      (interior_subset.trans Set.inter_subset_left) ⟨y, mem_interior_iff_mem_nhds.2 hW⟩
    have htW' := interior_subset htW
    have htU : t ∈ U := htW'.1
    have hpick : ∀ x ∈ T, ∃ z, z ∈ X ∩ B ∩ S x ∧ A z = t := by
      intro x hx
      have := Set.mem_iInter₂.1 htW'.2 x hx
      obtain ⟨z, hz, hAz⟩ := this
      exact ⟨z, hz, hAz⟩
    choose! z hz hAz using hpick
    have hinj : Set.InjOn z T := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.1 (hSdisj ha hb hne) (hz a ha).2 (hab ▸ (hz b hb).2)
    have hsub : z '' T ⊆ {x | x ∈ X ∩ B ∧ A x = t} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hz x hx).1, hAz x hx⟩
    have := (Set.encard_le_encard hsub).trans_eq (hcount t htU hgt)
    rw [hinj.encard_image, hTcard] at this
    exact absurd this (by norm_cast; omega)
  refine ⟨U, g, n, hUo, hy₀U, hUD, hgU, hgdU, hle, fun y hy hgy => ⟨hcount y hy hgy, ?_⟩⟩
  intro x hx hAx
  exact hsec y (hball hy) hgy x hx hAx

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

