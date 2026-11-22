import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTranslateFlagUnipotentHeightLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.FlagHeight

theorem exists_rat_translate_height_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C := by
  intro D S S₀ ρ d
  obtain ⟨KU, hKU, hU⟩ := GlobalTheory.UnitU.cocompact D ρ
  obtain ⟨KR, hKR, hR⟩ := GlobalTheory.Unf.FlagSub.radX_cocompact d
  have hlv : Continuous (GlobalTheory.JacMeas.lv d) := d.continuous_levi.comp continuous_subtype_val
  have hc : Continuous fun q : radX d × UX D ρ => q.1.1 * GlobalTheory.JacMeas.lv d q.2 :=
    (continuous_subtype_val.comp continuous_fst).mul (hlv.comp continuous_snd)
  have hK : IsCompact ((fun q : radX d × UX D ρ => q.1.1 * GlobalTheory.JacMeas.lv d q.2) '' (KR ×ˢ KU)) :=
    (hKR.prod hKU).image hc
  obtain ⟨C, hC⟩ := exists_height_le_of_isCompact S hK
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨n₀, hn₀, u, rfl⟩ := GlobalTheory.JacMeas.exists_rad_lv d hn
  obtain ⟨γu, hγu, k, hk, rfl⟩ := hU u
  have hr : (GlobalTheory.JacMeas.lv d γu)⁻¹ * n₀ * ((GlobalTheory.JacMeas.lv d γu)⁻¹)⁻¹ ∈ radX d := by
    have := GlobalTheory.JacMeas.lv_conj d n₀ hn₀ γu⁻¹
    simpa [map_inv] using this
  obtain ⟨γr, hγr, kr, hkr, hrk⟩ := hR ⟨_, hr⟩
  have hlvQ : GlobalTheory.JacMeas.lv d γu ∈ GQ S := d.levi_mem_GQ hγu.1 hγu.2
  have hγrQ : (γr : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 hγr
  refine ⟨(γr : GA D S)⁻¹ * (GlobalTheory.JacMeas.lv d γu)⁻¹, mul_mem (inv_mem hγrQ) (inv_mem hlvQ),
    mul_mem (inv_mem (GlobalTheory.JacMeas.radX_le d γr.2)) (inv_mem (GlobalTheory.JacMeas.lv_mem d γu)), ?_⟩
  apply hC
  refine ⟨(kr, k), ⟨hkr, hk⟩, ?_⟩
  have e : ((γr : GA D S) * kr) = (GlobalTheory.JacMeas.lv d γu)⁻¹ * n₀ * ((GlobalTheory.JacMeas.lv d γu)⁻¹)⁻¹ := by
    have := congrArg Subtype.val hrk
    simpa using this.symm
  simp only
  rw [map_mul]
  calc (kr : GA D S) * GlobalTheory.JacMeas.lv d k
      = (γr : GA D S)⁻¹ * ((γr : GA D S) * kr) * GlobalTheory.JacMeas.lv d k := by group
    _ = _ := by rw [e]; group

end GlobalTheory.FlagHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProducts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.StairUnit

theorem exists_mem_modul_notMem {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) u ∈ P.modul sc := by
  have h : ∀ v' : GlobalTheory.FinPl.Pl D, ∃ x : 𝓞 D.host.F, x ∉ v.asIdeal ∧ (v' ∈ P.S0 → x ∈ v'.asIdeal) := by
    intro v'
    by_cases h' : v' ∈ P.S0
    · have hn : ¬ v'.asIdeal ≤ v.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle) ▸ h')
      obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
      exact ⟨x, hx', fun _ => hx⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h h'⟩
  choose x hx hx' using h
  refine ⟨∏ v' ∈ P.S0, x v' ^ P.depth sc v', fun hu => ?_, ?_⟩
  · haveI := v.isPrime
    obtain ⟨v', -, h'⟩ := Ideal.IsPrime.prod_mem_iff.1 hu
    exact hx v' (v.isPrime.mem_of_pow_mem _ h')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' h' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 : x v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w h']; exact hx' v' h'
    exact h1

theorem mem_span_of_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E] {A B A' B' C : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', star x ∈ A) (hB : ∀ x ∈ B', star x ∈ B) {t : E} (ht : t ∈ A' * B' * C) :
    t ∈ Submodule.span (𝓞 E) {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c} := by
  refine FractionalIdeal.mul_induction_on ht (fun x hx c hc => ?_) fun x y => Submodule.add_mem _
  refine FractionalIdeal.mul_induction_on (C := fun x => x * c ∈ Submodule.span (𝓞 E)
    {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c}) hx (fun a ha b hb => ?_) fun x y hx hy => ?_
  · exact Submodule.subset_span ⟨_, hA a ha, _, hB b hb, c, hc, by rw [star_mul', star_star, star_star]⟩
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

theorem exists_unit_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  intro D T L sc G ρ p q hpq v hv
  obtain ⟨u, hu, hum⟩ := exists_mem_modul_notMem G.pl sc v hv
  refine ⟨u, hu, ?_⟩
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨hAA, hAAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hne : ∀ {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}, I ≠ 0 → (∀ x, x ∈ J ↔ star x ∈ I) → J ≠ 0 := by
    intro I J hI hJ h0
    apply hI
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h2 := h0 _ ((hJ (star y)).2 (by rwa [star_star]))
    rwa [star_eq_zero] at h2
  have hAb := hne hA hconj
  have hAAb := hne hAA hAAc
  have hB : ∀ x ∈ (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹,
      star x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q := by
    intro x hx
    have h1 := (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ q.rev).2 (star x)
    rw [Fin.rev_rev, star_star] at h1
    exact h1.2 hx
  have key : D.host.AAbar * (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹ *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p =
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have hq := q.2
    have e1 : 2 * ρ + 1 - 1 - q.rev.1 = q.1 + 1 := by rw [Fin.val_rev]; omega
    have e2 : q.rev.1 + 1 = p.1 := by rw [Fin.val_rev]; omega
    have e3 : 2 * ρ + 2 - 1 - p.1 = q.1 + 1 := by omega
    have e4 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
        D.host.AAbar * (G.pl.stAbar sc)⁻¹ := by
      rw [Places.stAbar, mul_inv, inv_inv, mul_inv_cancel_left₀ hAAb]
    unfold stairId
    rw [e1, e2, e3, e4, pow_succ (G.pl.stAbar sc) p.1]
    have h1 : G.pl.stA sc ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hA
    have h2 : G.pl.stAbar sc ^ p.1 ≠ 0 := pow_ne_zero _ hAb
    field_simp
  have hmem : ((u : D.host.F) : D.host.E) ∈
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hum, rfl⟩
  rw [← key] at hmem
  have h := mem_span_of_mem_mul (fun x hx => (hAAc x).1 hx) hB hmem
  simp only [hs] at h
  exact h

end GlobalTheory.StairUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.PrincipalMove

open GlobalTheory.FinPlLoc

theorem exists_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  intro D W ρ x Q g k u hg hk hM
  set e : AE D := idem D Q with he_def
  have he : e * e = e := idem_mul_self Q
  have hr : g * k ∈ grpAt W Q := mul_mem hg hk
  set U : Matrix (Fin ρ) (Fin ρ) (AE D) := u.1.1 with hU
  have hu : ∀ i j : Fin ρ, (j < i → U i j = 0) ∧ U i i = 1 := fun i j => u.2 i j
  let u' : GL (Fin ρ) (AE D) := mixGL he u.1 1
  have hu'v : u'.val = e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := rfl
  have hu' : u' ∈ UX D ρ := by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · show u'.val i j = 0
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i j).1 hij, Matrix.one_apply_ne hij.ne']
    · show u'.val i i = 1
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i i).2]
  refine ⟨g * k, ⟨u', hu', ?_⟩, hr, by group⟩
  have heM : e • (mt W k ⬝ x - mt W g⁻¹ ⬝ (x ⬝ U)) = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact (mem_idOff_iff Q _).1 (hM i j)
  have hgg : mt W g * mt W g⁻¹ = 1 := by
    rw [← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one]
  have h1 : e • (mt W (g * k) ⬝ x) = e • (x ⬝ U) := by
    have : mt W (g * k) ⬝ x = x ⬝ U + mt W g ⬝ (mt W k ⬝ x - mt W g⁻¹ ⬝ (x ⬝ U)) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc (mt W g) (mt W g⁻¹), hgg, Matrix.one_mul, FinPlLoc.mt_mul, Matrix.mul_assoc]
      abel
    rw [this, smul_add, ← Matrix.mul_smul (mt W g), heM, Matrix.mul_zero, add_zero]
  have h2 : (1 - e) • (mt W (g * k) ⬝ x) = (1 - e) • x := by
    have hm := (mem_grpAt_iff Q (g * k)).1 hr
    have : (1 - e) • mt W (g * k) = (1 - e) • (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) := by
      conv_lhs => rw [← hm]
      simp only [mix, smul_add, smul_smul]
      have h3 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
      have h4 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
      rw [h3, h4, zero_smul, zero_add]
    rw [← Matrix.smul_mul, this, Matrix.smul_mul, Matrix.one_mul]
  show mt W (g * k) ⬝ x = x ⬝ u'.val
  rw [hu'v]
  calc mt W (g * k) ⬝ x = e • (mt W (g * k) ⬝ x) + (1 - e) • (mt W (g * k) ⬝ x) := by
        rw [← add_smul, add_sub_cancel, one_smul]
    _ = e • (x ⬝ U) + (1 - e) • x := by rw [h1, h2]
    _ = x ⬝ (e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D))) := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]

end GlobalTheory.PrincipalMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtendRestrictionFinitePointsEq
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicRestrict

theorem ext_restrict {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W)
    (hΨ : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) (h : GA D V) :
    c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  set h₀ := GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h) with eh₀
  have m₀ : h₀ ∈ GfC V := GlobalTheory.AdelicScalar.finLift_mem V _
  have s₀ : finHom V h₀ = finHom V h :=
    congrArg Subtype.val (GlobalTheory.AdelicScalar.finLift_spec V ((finHom V).rangeRestrict h))
  set k := h₀⁻¹ * h with ek
  have hk1 : finHom V k = 1 := by rw [ek, map_mul, map_inv, s₀, inv_mul_cancel]
  have hkE : Lev.finE V k = 1 := by
    unfold Lev.finE
    rw [MonoidHom.comp_apply, hk1, map_one]
  have hkL : Lev.finE V k ∈ lev D.sp.cm V.gram β L := by rw [hkE]; exact Subgroup.one_mem _
  have hχ : Lev.levChi V β L k = 1 := by
    unfold Lev.levChi
    rw [hkE]
    have := map_one (levChar D.sp.cm V.gram β L)
    have e : levFn β L 1 = (levChar D.sp.cm V.gram β L 1 : ℂˣ) := rfl
    rw [e, this]
    rfl
  have hlaw := hΨ 1 (Subgroup.one_mem _) k hkL h₀
  have eh : 1 * h₀ * k = h := by rw [ek, one_mul, mul_inv_cancel_left]
  rw [eh, hχ, one_smul] at hlaw
  change c.ρ h⁻¹ (Ψ (GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h))) = Ψ h
  rw [← eh₀, hlaw]
  have hρ : c.ρ h⁻¹ = c.ρ k⁻¹ := by
    rw [← eh, one_mul, _root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem m₀), mul_one]
  rw [hρ]

end GlobalTheory.AdelicRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtremalVectorValuesLoweringAndTorus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExtFock

section Perm

variable {n : ℕ} (π : Fin n → Fin n)

theorem submatrix_eq_mul (P : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π = P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply]

variable {π}

theorem perm_mul_self (hπ : ∀ a, π (π a) = a) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
  simp [mul_ite, Finset.sum_ite_eq', hπ]

theorem perm_single_perm (hπ : ∀ a, π (π a) = a) (c d : Fin n) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.single c d 1 * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.single (π c) (π d) 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.single_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  have key : ∀ x y, x = π y ↔ π x = y := fun x y => ⟨fun h => by rw [h, hπ], fun h => by rw [← h, hπ]⟩
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [key d b]
  by_cases h1 : π c = a
  · subst h1; simp
  · have h2 : ¬ a = π c := fun h => h1 h.symm
    simp [h1, h2]

theorem perm_diag_perm (hπ : ∀ a, π (π a) = a) (t : Fin n → ℂ) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.diagonal t * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.diagonal (fun a => t (π a)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.diagonal_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  split_ifs with h
  · rw [h]
  · rfl

theorem conj_submatrix (hπ : ∀ a, π (π a) = a) (P X : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π * X * (P.submatrix id π)⁻¹ =
      P * ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * X * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π) * P⁻¹ := by
  rw [submatrix_eq_mul π P, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (perm_mul_self hπ)]
  simp only [Matrix.mul_assoc]

end Perm

theorem killPair_rev {n p : ℕ} (hpn : p ≤ n) {c d : Fin n} (h : d < c) :
    GlobalTheory.HolRead.KillPair (fun a : Fin n => decide ((a : ℕ) < p)) (GlobalTheory.AdSpan.revPos p c) (GlobalTheory.AdSpan.revPos p d) := by
  have hdc : (d : ℕ) < c := h
  unfold GlobalTheory.HolRead.KillPair GlobalTheory.AdSpan.revPos
  by_cases hc : (c : ℕ) < p <;> by_cases hd : (d : ℕ) < p
  · left
    simp only [dif_pos (And.intro hc hpn), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, by omega⟩
  · omega
  · right; right
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by omega⟩
  · right; left
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_neg (fun h' : (d : ℕ) < p ∧ p ≤ n => hd h'.1), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, hdc⟩

end GlobalTheory.ExtFock

namespace GlobalTheory.ExtFock

set_option maxHeartbeats 4000000 in

theorem ext_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (p : ℕ), (∀ τ, ((Wc D i).sig (tauE D τ)).1 = p) → p ≤ (Wc D i).rank → IsExtVec (R.MW i (sg0 D A)) (fun ρ => u ρ) → ∀ T ∈ R.Wall i (sg0 D A), LowKilled R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) (T fun ρ => u ρ) ∧ ∀ (ρ : D.what₂.Tau) (s : Fin (Wc D i).rank → ℝ), ∃ l : ℂ, R.ωP i t (1, torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) = l • R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w) ∧ ∀ g, T (fun ρ => u ρ) (g * torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) = l * T (fun ρ => u ρ) g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hP i t u w p hp hpn hext T hT
  have hTm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  have hθ : IsInfFam R.θ := hM.inf
  have hεd : ∀ ρ, (R.MW i (sg0 D A)).ε ρ = fun a : Fin (Wc D i).rank => decide ((a : ℕ) < p) := by
    intro ρ; funext a; rw [hM.order i ρ a, hp ρ]
  have hε : ∀ ρ (a : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε ρ a = if (a : ℕ) < p then true else !true := by
    intro ρ a; rw [hεd ρ]; by_cases h : (a : ℕ) < p <;> simp [h]
  have KW := fun ρ => GlobalTheory.HolRead.ExtKill.kill_and_weight D R.θ (Wc D i) _ (R.MW i (sg0 D A)) _ _ T hθ hTm
    (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ)) hext ρ p true (hε ρ)
  have hπ : ∀ a : Fin (Wc D i).rank, revPos p (revPos p a) = a := revPos_revPos p
  have hinv : ∀ ρ, ((onb (R.MW i (sg0 D A)) ρ))⁻¹ = (R.MW i (sg0 D A)).fr ρ := fun ρ =>
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))
  refine ⟨⟨(hTm.aut _).smooth, fun ρ c d hdc => ?_⟩, fun ρ s => ?_⟩
  · have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.single c d 1 * (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.single (revPos p c) (revPos p d) 1 * (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_single_perm hπ, hinv]
      rfl
    rw [e]
    apply (KW ρ).1
    rw [hεd ρ]
    exact killPair_rev hpn hdc
  · set l : ℂ := Complex.exp (((∑ a, extWt (R.MW i (sg0 D A)) ρ a * s (revPos p a) : ℝ) : ℂ) * Complex.I) with hl
    have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) *
        (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) *
          (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_diag_perm hπ, hinv]
      rfl
    have htor : torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s =
        atTau R.θ (Wc D i) ρ (((R.MW i (sg0 D A)).fr ρ)⁻¹ *
          Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) * (R.MW i (sg0 D A)).fr ρ) := by
      unfold torAt; rw [e]
    refine ⟨l, ?_, fun g => ?_⟩
    · have hK := Formalism.IndefR.FWT.diag_mem (ε := (R.MW i (sg0 D A)).ε ρ) (fun a => s (revPos p a))
      obtain ⟨-, -, hwt⟩ := hext ρ
      have h2 := (hP.ioP i t).2.1 ρ _ hK u (l • u ρ) (by
        show l • (((u ρ : (R.MW i (sg0 D A)).sm ρ)) : (R.MW i (sg0 D A)).H ρ) = _
        rw [hwt _ hK]) w
      rw [htor, h2, MultilinearMap.map_update_smul, Function.update_eq_self, map_smul, LinearMap.smul_apply]
      unfold RealDat.ptP
      exact map_smul _ _ _
    · rw [htor]
      exact (KW ρ).2 _ g

end GlobalTheory.ExtFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapNonvanishingConditionLocalise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LocCond

variable {D : D7}

theorem idAt_mul_idOff {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) :
    a * b = 0 := by
  have h1 := (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 ha
  have h2 := (GlobalTheory.FinPlLoc.mem_idOff_iff P b).1 hb
  calc a * b = (GlobalTheory.FinPlLoc.idem D P * a) * b := by rw [h1]
    _ = a * (GlobalTheory.FinPlLoc.idem D P * b) := by ring
    _ = 0 := by rw [h2, mul_zero]

theorem idOff_true_le {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idOff D (fun _ => True)) : a ∈ idOff D P := by
  unfold GlobalTheory.FinPl.idOff at *
  rw [Submodule.mem_iInf] at *
  intro w
  exact ha ⟨w.1, trivial⟩

theorem idAt_le_true {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt at *
  obtain ⟨h0, -⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem mul_mem_left' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hE i l)

theorem mul_mem_right' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hZ l j)

theorem mul_eq_zero_of {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ idOff D P) (hZ : ∀ i j, Z i j ∈ idAt D P) :
    E ⬝ Z = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idAt_mul_idOff (hZ l j) (hE i l)

theorem off_entries {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) :
    ∀ i j, (mt S g - 1) i j ∈ idOff D P := fun i j => by
  rw [Matrix.sub_apply]
  exact (GlobalTheory.FinPlLoc.mem_congGrp _ g).1 hg i j

theorem mt_off_mul {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) {k : ℕ}
    (Z : Matrix (Fin S.rank) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ idAt D P) : mt S g ⬝ Z = Z := by
  calc mt S g ⬝ Z = (mt S g - 1) ⬝ Z + Z := by rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    _ = Z := by rw [mul_eq_zero_of _ _ (off_entries hg) hZ, zero_add]

end GlobalTheory.AscFin.LocCond

open GlobalTheory.AscFin.LocCond in

theorem GlobalTheory.AscFin.cond_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : GlobalTheory.FinPl.Pl D → Prop) (h₁ h₂ : GA D W), h₁ ∈ grpAt W P → h₂ ∈ grpOff W P → Cond dW p x y ψ (fun _ => True) (h₁ * h₂) → Cond dW p x y ψ P h₁ := by
  intro D ψ _ V V₀ W W₀ ρ σ dV dW p x y P h₁ h₂ _ h2 hc
  have e2 := off_entries (inv_mem h2)
  have hinv : mt W (h₁ * h₂)⁻¹ = mt W h₂⁻¹ ⬝ mt W h₁⁻¹ := by
    rw [_root_.mul_inv_rev, GlobalTheory.FinPlLoc.mt_mul]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := hc.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have hk := idOff_true_le (P := P) (hoff i j)
    have hm := mul_mem_left' (mt W h₂⁻¹ - 1) (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) e2 i j
    have eq : mt W h₁⁻¹ ⬝ (x ⬝ u.1.1) - x - a =
        (mt W (h₁ * h₂)⁻¹ ⬝ (x ⬝ u.1.1) - x - a) - (mt W h₂⁻¹ - 1) ⬝ (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) := by
      rw [hinv, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [eq, Matrix.sub_apply]
    exact sub_mem hk hm
  · intro N hN hlow hA
    refine hc.shift N (fun i j => idAt_le_true (hN i j)) hlow ?_
    have hZ : ∀ i j, (mt W h₁⁻¹ ⬝ (x ⬝ N)) i j ∈ idAt D P := mul_mem_right' _ _ (mul_mem_right' _ _ hN)
    rw [hinv, Matrix.mul_assoc, mt_off_mul (inv_mem h2) _ hZ]
    exact hA
  · intro ξ hξ ξ' hP heq
    refine hc.iso ξ hξ ξ' (fun i j => idAt_le_true (hP i j)) ?_
    have hZ : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D P := by
      rw [HypDec.incX_apply]
      exact mul_mem_right' _ _ hP
    rw [GlobalTheory.FinPlLoc.mt_mul, Matrix.mul_assoc, mt_off_mul h2 _ hZ]
    exact heq

end
end

