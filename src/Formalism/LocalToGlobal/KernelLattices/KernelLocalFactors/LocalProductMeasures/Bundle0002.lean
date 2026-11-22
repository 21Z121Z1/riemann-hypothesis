import Mathlib
import Formalism.LocalToGlobal.KernelLattices.Bundle0002
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapENe
import Formalism.LocalToGlobal.Divisibility.Bundle0001

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.TwistValueAtUniformizer
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.UG Formalism.UG.P

section XV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def xvY (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E) : RInt F E := toRInt F E b * quE E v + (1 - quE E v)

theorem xv_coe (v : HeightOneSpectrum (𝓞 F)) (w : Eˣ) (b : 𝓞 E) (hw : (w : E) = (b : E)) :
    ((xvY v b : RInt F E) : AfE F E) = ((locId E v w : (AfE F E)ˣ) : AfE F E) := by
  show ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1) + (1 - (1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1) =
    (w : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hw, TensorProduct.tmul_sub]
  rfl

theorem xv_supp (v : HeightOneSpectrum (𝓞 F)) (w : Eˣ) : locId E v w ∈ suppAt E v := by
  unfold suppAt
  rw [Subgroup.mem_iInf]
  intro v'
  rw [Subgroup.mem_iInf]
  intro hne
  rw [MonoidHom.mem_ker]
  apply Units.ext
  show (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v')) ((w : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) = 1
  rw [map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_sub, Formalism.L2.G.sgl_apply_ne F v 1 hne,
    TensorProduct.tmul_zero, zero_add, sub_zero, map_one (evalV F v')]
  rfl

theorem xv_cong (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hv : P.asIdeal.under (𝓞 F) = v.asIdeal) (b t : 𝓞 E) (k : ℕ)
    (h : b - t ∈ P.asIdeal ^ k) : xvY v b - toRInt F E t ∈ (P.asIdeal ^ k).map (toRInt F E) := by
  have e : xvY v b - toRInt F E t = toRInt F E (b - t) * quE E v + toRInt F E (1 - t) * (1 - quE E v) := by
    unfold xvY
    rw [map_sub, map_sub, map_one]; ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h)) (Ideal.mul_mem_left _ _ (qu_one_sub_mem v _ k ?_))
  intro a ha
  have h1 : algebraMap (𝓞 F) (𝓞 E) a ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E)) := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ k h1
  rw [Ideal.map_le_iff_le_comap, ← hv]

theorem xv_other (v : HeightOneSpectrum (𝓞 F)) (P' : HeightOneSpectrum (𝓞 E)) (b : 𝓞 E)
    (h : P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) : xvY v b - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  have e : xvY v b - 1 = toRInt F E (b - 1) * quE E v := by
    unfold xvY
    rw [map_sub, map_one]; ring
  rw [e]
  by_cases hP' : P'.asIdeal.under (𝓞 F) = v.asIdeal
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h hP'))
  · refine Ideal.mul_mem_left _ _ ?_
    have hex : ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ P'.asIdeal ∧ a ∉ v.asIdeal := by
      by_contra hcon
      push Not at hcon
      apply hP'
      have hle : P'.asIdeal.under (𝓞 F) ≤ v.asIdeal := fun a ha => hcon a ha
      have hbot : P'.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P'.ne_bot
      have hpr : (P'.asIdeal.under (𝓞 F)).IsPrime := inferInstance
      exact (hpr.isMaximal hbot).eq_of_le v.isPrime.ne_top hle
    obtain ⟨a, ha1, ha2⟩ := hex
    exact qu_eps_mem v _ a ha1 ha2

theorem xv_top (P : HeightOneSpectrum (𝓞 E)) (K : Ideal (RInt F E)) (hK : ∀ P' : HeightOneSpectrum (𝓞 E), P'.asIdeal.map (toRInt F E) ⊔ K = ⊤)
    (D : 𝓞 F) (hD0 : D ≠ 0) (hD : toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) ∈ K) : K = ⊤ := by
  have hI : Ideal.span {algebraMap (𝓞 F) (𝓞 E) D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    intro h
    apply adelstab_algebraMap_ne_zero (E := E) D hD0
    rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero]
  obtain ⟨n, hn⟩ := qe_strip P K (fun P' _ => hK P') _ hI 0 (by
    rw [pow_zero, one_mul, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; exact hD)
  have h1 : (P.asIdeal.map (toRInt F E)) ^ n ⊔ K = ⊤ := Ideal.pow_sup_eq_top (hK P)
  rw [← Ideal.map_pow, sup_eq_right.2 hn] at h1
  exact h1

variable {L : Type} [Field L]

theorem xv_same (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) (hξ : inertAt E v ≤ ξ.ker) (P : HeightOneSpectrum (𝓞 E)) (q q' : 𝓞 E)
    (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2) (hq' : q' ∈ P.asIdeal) (hq2' : q' ∉ P.asIdeal ^ 2) (y y' : (AfE F E)ˣ) (y₀ y₀' : RInt F E)
    (hy : (y₀ : AfE F E) = (y : AfE F E)) (hy' : (y₀' : AfE F E) = (y' : AfE F E)) (hs : y ∈ suppAt E v) (hs' : y' ∈ suppAt E v)
    (h1 : y₀ - toRInt F E q ∈ (P.asIdeal ^ 2).map (toRInt F E)) (h1' : y₀' - toRInt F E q' ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E))
    (h2' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀' - 1 ∈ P'.asIdeal.map (toRInt F E)) : ξ y = ξ y' := by
  have hle := qe_le P y y₀ hy q hq hq2 h1 h2
  have hle' := qe_le P y' y₀' hy' q' hq' hq2' h1' h2'
  have hmem : ∀ (z₀ : RInt F E) (c : 𝓞 E), c ∈ P.asIdeal → z₀ - toRInt F E c ∈ (P.asIdeal ^ 2).map (toRInt F E) → z₀ ∈ P.asIdeal.map (toRInt F E) := by
    intro z₀ c hc hz
    have e : z₀ = (z₀ - toRInt F E c) + toRInt F E c := by ring
    rw [e]
    exact add_mem (Ideal.map_mono (Ideal.pow_le_self two_ne_zero) hz) (Ideal.mem_map_of_mem _ hc)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hle' (hmem y₀ q hq h1))
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (hle (hmem y₀' q' hq' h1'))
  have haa : a * a' = 1 := by
    have e0 : a * a' * y₀ = y₀ := by rw [mul_assoc, ha', ha]
    have e1 : ((a * a' : RInt F E) : AfE F E) * (y : AfE F E) = 1 * (y : AfE F E) := by
      rw [one_mul, ← hy]
      exact congrArg Subtype.val e0
    exact Subtype.ext (y.isUnit.mul_right_cancel e1)
  let u : (RInt F E)ˣ := ⟨a, a', haa, by rw [mul_comm]; exact haa⟩
  have hu : Units.map (RInt F E).subtype.toMonoidHom u = y * y'⁻¹ := by
    apply Units.ext
    show (a : AfE F E) = (y : AfE F E) * ((y'⁻¹ : (AfE F E)ˣ) : AfE F E)
    have e2 : (a : AfE F E) * (y' : AfE F E) = (y : AfE F E) := by
      rw [← hy, ← hy']
      exact congrArg Subtype.val ha
    rw [← e2, mul_assoc, Units.mul_inv, mul_one]
  have hw : Units.map (RInt F E).subtype.toMonoidHom u ∈ inertAt E v := by
    refine Subgroup.mem_inf.2 ⟨?_, by rw [hu]; exact mul_mem hs (inv_mem hs')⟩
    show _ ∈ (RInt F E).toSubmonoid.units
    rw [Submonoid.mem_units_iff]
    exact ⟨a.2, a'.2⟩
  have h3 := hξ hw
  rw [hu, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

end XV

theorem xv_tame {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] {S : Set ℕ}
    (ξ : Tup F E L S) (v : HeightOneSpectrum (𝓞 F)) : wildAt E v ≤ (ξ : Chr F E L).ker :=
  mem_kills.1 ((Subgroup.mem_iInf.1 ξ.2.1.2) v)

theorem twist_value_at_q : XiQ := by
  intro F E _ _ _ _ _ L _ S ξ v P hv hq w b hw hb1 hb2
  exact qVal_spec_tup ξ P hq v hv (locId E v w) (xvY v b) (xv_coe v w b hw) (xv_supp v w) (xv_cong v P hv b _ 2 hb1)
    (fun P' hne => xv_other v P' b (hb2 P' hne))

theorem twist_residue_character : XiRes := by
  intro F E _ _ _ _ _ L _ S ξ v P hv w b r hw hb hb2
  have hbP : b ∉ P.asIdeal := by
    intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem, hb] at h
    exact r.ne_zero h
  have hc1 : xvY (F := F) v b - toRInt F E b ∈ P.asIdeal.map (toRInt F E) := by
    have := xv_cong v P hv b b 1 (by rw [sub_self]; exact zero_mem _)
    rwa [pow_one] at this
  have hoth : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → xvY (F := F) v b - 1 ∈ P'.asIdeal.map (toRInt F E) :=
    fun P' hne => xv_other v P' b (hb2 P' hne)
  have hy0 : xvY (F := F) v b ∈ Ideal.span {xvY (F := F) v b} := Ideal.mem_span_singleton_self _
  have hK : ∀ P' : HeightOneSpectrum (𝓞 E), P'.asIdeal.map (toRInt F E) ⊔ Ideal.span {xvY (F := F) v b} = ⊤ := by
    intro P'
    rw [Ideal.eq_top_iff_one]
    by_cases hP' : P' = P
    · rw [hP']
      obtain ⟨b', i, hi, hbi⟩ := P.isMaximal.exists_inv hbP
      have e3 := congrArg (toRInt F E) hbi
      simp only [map_add, map_mul, map_one] at e3
      have e : (1 : RInt F E) = (toRInt F E i - (xvY (F := F) v b - toRInt F E b) * toRInt F E b') + xvY (F := F) v b * toRInt F E b' := by
        linear_combination -e3
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (sub_mem (Ideal.mem_map_of_mem _ hi) (Ideal.mul_mem_right _ _ hc1)))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hy0))
    · have e : (1 : RInt F E) = -(xvY (F := F) v b - 1) + xvY (F := F) v b := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (neg_mem (hoth P' hP'))) (Ideal.mem_sup_right hy0)
  obtain ⟨D, hD0, hD⟩ := qe_denom (locId E v w) (xvY v b) (xv_coe v w b hw)
  have htop := xv_top P _ hK D hD0 hD
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 ((Ideal.eq_top_iff_one _).1 htop)
  let u : (RInt F E)ˣ := ⟨xvY v b, a, by rw [mul_comm]; exact ha, ha⟩
  have hu : Units.map (RInt F E).subtype.toMonoidHom u = locId E v w := Units.ext (xv_coe v w b hw)
  have h := b_resChar_spec (ξ : Chr F E L) (xv_tame ξ) P v hv u r b hb (by rw [hu]; exact xv_supp v w) hc1 hoth
  rw [hu] at h
  exact h

theorem twist_value_at_uniformizer : XiUnif := by
  intro F E _ _ _ _ _ L _ S ξ v P hv hQ w b hw hb1 hb2 hb3
  have hin : inertAt E v ≤ (ξ : Chr F E L).ker := by
    by_contra h
    exact hQ h
  have hY1 : xvY (F := F) v b - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) := xv_cong v P hv b b 2 (by rw [sub_self]; exact zero_mem _)
  have hY2 : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → xvY (F := F) v b - 1 ∈ P'.asIdeal.map (toRInt F E) :=
    fun P' hne => xv_other v P' b (hb3 P' hne)
  have hex : ∃ k, IsUnifVal (ξ : Chr F E L) P k := by
    refine ⟨(ξ : Chr F E L) (locId E v w), fun v' hv' y y₀ b' hy hb1' hb2' hs h1 h2 => ?_⟩
    have hvv : v' = v := HeightOneSpectrum.ext (hv'.symm.trans hv)
    subst hvv
    exact xv_same (ξ : Chr F E L) v' hin P b' b hb1' hb2' hb1 hb2 y (locId E v' w) y₀ (xvY v' b) hy (xv_coe v' w b hw) hs (xv_supp v' w) h1 hY1 h2 hY2
  have hsp : IsUnifVal (ξ : Chr F E L) P (unifVal (ξ : Chr F E L) P) := by
    unfold unifVal
    rw [dif_pos hex]
    exact hex.choose_spec
  exact hsp v hv (locId E v w) (xvY v b) b (xv_coe v w b hw) hb1 hb2 (xv_supp v w) hY1 hY2

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.XiProd
section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Ker

open Formalism.L2.DIV Formalism.UG

section XP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def xpJ (d : FiniteAdeleRing (𝓞 F) F) (a : E) : AfE F E := a ⊗ₜ[F] d + (1 : E) ⊗ₜ[F] (1 - d)

theorem xp_J_locId (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ) : ((locId E v a : (AfE F E)ˣ) : AfE F E) = xpJ (Formalism.L2.G.sgl F v 1) (a : E) := rfl

theorem xp_J_zero (a : E) : xpJ (0 : FiniteAdeleRing (𝓞 F) F) a = 1 := by
  unfold xpJ
  rw [TensorProduct.tmul_zero, zero_add, sub_zero]
  rfl

theorem xp_J_one (a : E) : xpJ (1 : FiniteAdeleRing (𝓞 F) F) a = a ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) := by
  unfold xpJ
  rw [sub_self, TensorProduct.tmul_zero, add_zero]

theorem xp_J_orth {d d' : FiniteAdeleRing (𝓞 F) F} (h : d * d' = 0) (a : E) : xpJ d a * xpJ d' a = xpJ (d + d') a := by
  have h1 : d * (1 - d') = d := by rw [mul_sub, mul_one, h, sub_zero]
  have h2 : (1 - d) * d' = d' := by rw [_root_.sub_mul, one_mul, h, sub_zero]
  have h3 : (1 - d) * (1 - d') = 1 - (d + d') := by rw [_root_.sub_mul, one_mul, h1]; ring
  unfold xpJ
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, h, h1, h2, h3, TensorProduct.tmul_zero, zero_add, mul_one, one_mul, one_mul, TensorProduct.tmul_add]
  abel

theorem xp_J_same {d : FiniteAdeleRing (𝓞 F) F} (h : d * d = d) (a b : E) : xpJ d a * xpJ d b = xpJ d (a * b) := by
  have h2 : d * (1 - d) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  have h3 : (1 - d) * d = 0 := by rw [_root_.sub_mul, one_mul, h, sub_self]
  have h4 : (1 - d) * (1 - d) = 1 - d := by rw [mul_sub, mul_one, h3, sub_zero]
  unfold xpJ
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, h, h2, h3, h4, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero, zero_add, one_mul]

theorem xp_J_sub (d : FiniteAdeleRing (𝓞 F) F) (a : E) : xpJ d a = 1 + (a - 1) ⊗ₜ[F] d := by
  unfold xpJ
  rw [TensorProduct.tmul_sub, TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
  abel

theorem xp_scal (n : ℕ) (y : E) (g : FiniteAdeleRing (𝓞 F) F) :
    y ⊗ₜ[F] (((n : ℕ) : FiniteAdeleRing (𝓞 F) F) * g) = (((n : ℕ) : E) * y) ⊗ₜ[F] g := by
  have h1 : ((n : ℕ) : FiniteAdeleRing (𝓞 F) F) * g = ((n : ℕ) : F) • g := by rw [Algebra.smul_def, map_natCast]
  rw [h1, ← TensorProduct.smul_tmul, Algebra.smul_def, map_natCast]

theorem xp_J_eq (N k : ℕ) (a : E) (b : 𝓞 E) (hb : ((k : ℕ) : E) * (a - 1) = (b : E)) (g : FiniteAdeleRing (𝓞 F) F) (hg : g ∈ intAd F)
    (d : FiniteAdeleRing (𝓞 F) F) (hd : d = ((N * k : ℕ) : FiniteAdeleRing (𝓞 F) F) * g) :
    ∃ r : RInt F E, xpJ d a = ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) := by
  refine ⟨toRInt F E b * ⟨(1 : E) ⊗ₜ[F] g, qu_right g hg⟩, ?_⟩
  rw [xp_J_sub, hd, xp_scal]
  push_cast
  congr 1
  show _ = (N : AfE F E) * ((algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] g))
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  conv_rhs => rw [← nsmul_eq_mul, TensorProduct.smul_tmul', nsmul_eq_mul]
  rw [mul_assoc, hb]

theorem xp_J_at_one (d : FiniteAdeleRing (𝓞 F) F) : xpJ d (1 : E) = 1 := by
  unfold xpJ
  rw [← TensorProduct.tmul_add, add_sub_cancel]
  rfl

theorem xp_mem_congN (N k : ℕ) (a : Eˣ) (b b' : 𝓞 E) (hb : ((k : ℕ) : E) * ((a : E) - 1) = (b : E))
    (hb' : ((k : ℕ) : E) * (((a⁻¹ : Eˣ) : E) - 1) = (b' : E)) (g : FiniteAdeleRing (𝓞 F) F) (hg : g ∈ intAd F)
    (d : FiniteAdeleRing (𝓞 F) F) (hd : d = ((N * k : ℕ) : FiniteAdeleRing (𝓞 F) F) * g) (hdd : d * d = d)
    (u : (AfE F E)ˣ) (hu : (u : AfE F E) = xpJ d (a : E)) : u ∈ congN F E N := by
  obtain ⟨r, hr⟩ := xp_J_eq N k (a : E) b hb g hg d hd
  obtain ⟨r', hr'⟩ := xp_J_eq N k ((a⁻¹ : Eˣ) : E) b' hb' g hg d hd
  let u₀ : (RInt F E)ˣ :=
    { val := 1 + (N : RInt F E) * r
      inv := 1 + (N : RInt F E) * r'
      val_inv := Subtype.ext (by
        show ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) * ((1 + (N : RInt F E) * r' : RInt F E) : AfE F E) = 1
        rw [← hr, ← hr', xp_J_same hdd, Units.mul_inv, xp_J_at_one])
      inv_val := Subtype.ext (by
        show ((1 + (N : RInt F E) * r' : RInt F E) : AfE F E) * ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) = 1
        rw [← hr, ← hr', xp_J_same hdd, Units.inv_mul, xp_J_at_one]) }
  unfold congN congU
  rw [Subgroup.mem_map]
  refine ⟨u₀, (mem_kerRed _ u₀).2 ?_, Units.ext ?_⟩
  · show 1 + (N : RInt F E) * r - 1 ∈ _
    rw [add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · show ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) = u
    rw [← hr, hu]

theorem xp_g (M : ℕ) (hM : 0 < M) (d : FiniteAdeleRing (𝓞 F) F) (hd : d ∈ intAd F)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∈ v.asIdeal → evalV F v d = 0) :
    ∃ g ∈ intAd F, d = ((M : ℕ) : FiniteAdeleRing (𝓞 F) F) * g := by
  have hM0 : ((M : ℕ) : F) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) ((M : ℕ) : F)⁻¹ * d, ?_, ?_⟩
  · intro v
    show algebraMap F (v.adicCompletion F) ((M : ℕ) : F)⁻¹ * d v ∈ v.adicCompletionIntegers F
    by_cases hv : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal
    · have h0 : d v = 0 := hT v hv
      rw [h0, mul_zero]
      exact zero_mem _
    · have hval : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ((M : ℕ) : 𝓞 F))) = 1 := by
        rw [Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R, intValuation_eq_one_iff_mem_primeCompl]
        exact Ideal.mem_primeCompl_iff.mpr hv
      rw [map_natCast] at hval
      rw [mem_adicCompletionIntegers, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hd v
  · rw [← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]

def xpE (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ T, Formalism.L2.G.sgl F v 1

open Classical in
theorem xp_E_at (T : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    evalV F w (xpE T) = if w ∈ T then 1 else 0 := by
  unfold xpE
  rw [map_sum]
  split_ifs with hw
  · rw [Finset.sum_eq_single w (fun b _ hb => Formalism.L2.G.sgl_apply_ne F b 1 (Ne.symm hb)) (fun h => absurd hw h), Formalism.L2.G.sgl_apply_same]
  · exact Finset.sum_eq_zero fun b hb => Formalism.L2.G.sgl_apply_ne F b 1 (fun h => hw (h ▸ hb))

theorem xp_E_idem (T : Finset (HeightOneSpectrum (𝓞 F))) : xpE T * xpE T = xpE T := by
  classical
  apply Formalism.L2.G.adele_ext
  intro w
  rw [map_mul, xp_E_at]
  split_ifs <;> simp

theorem xp_E_compl_idem (T : Finset (HeightOneSpectrum (𝓞 F))) : (1 - xpE T) * (1 - xpE T) = 1 - xpE T := by
  rw [mul_sub, mul_one, _root_.sub_mul, one_mul, xp_E_idem, sub_self, sub_zero]

theorem xp_E_orth (T : Finset (HeightOneSpectrum (𝓞 F))) : xpE T * (1 - xpE T) = 0 := by
  rw [mul_sub, mul_one, xp_E_idem, sub_self]

theorem xp_sgl_orth (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
    Formalism.L2.G.sgl F v 1 * xpE T = 0 := by
  classical
  apply Formalism.L2.G.adele_ext
  intro w
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    rw [xp_E_at, if_neg hv, mul_zero]
  · rw [Formalism.L2.G.sgl_apply_ne F v 1 h, zero_mul]

theorem xp_E_int (T : Finset (HeightOneSpectrum (𝓞 F))) : xpE T ∈ intAd F :=
  Subring.sum_mem _ fun v _ => qu_sgl_int v 1 (one_mem _)

theorem xp_prod (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Eˣ) :
    ((∏ v ∈ T, locId E v x : (AfE F E)ˣ) : AfE F E) = xpJ (xpE T) (x : E) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Units.val_one, xpE, Finset.sum_empty, xp_J_zero]
  | insert v T hv ih =>
    rw [Finset.prod_insert hv, Units.val_mul, ih, xp_J_locId, xp_J_orth (xp_sgl_orth T v hv)]
    unfold xpE
    rw [Finset.sum_insert hv]

theorem xp_den (a : E) : ∃ k : ℕ, 0 < k ∧ ∃ c : 𝓞 E, ((k : ℕ) : E) * a = (c : E) := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hI : Ideal.span {q} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hk : Ideal.absNorm (Ideal.span {q}) ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {q}))
  refine ⟨Ideal.absNorm (Ideal.span {q}), Nat.pos_of_ne_zero hk, t * p, ?_⟩
  have hqE : algebraMap (𝓞 E) E q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hq0
  rw [← map_natCast (algebraMap (𝓞 E) E), ← ht]
  show algebraMap (𝓞 E) E (t * q) * _ = algebraMap (𝓞 E) E (t * p)
  rw [map_mul, map_mul]
  field_simp

theorem unit_sub_one_bounded_denominator (x : Eˣ) : ∃ k : ℕ, 0 < k ∧ ∃ b b' : 𝓞 E, ((k : ℕ) : E) * ((x : E) - 1) = (b : E) ∧
    ((k : ℕ) : E) * (((x⁻¹ : Eˣ) : E) - 1) = (b' : E) := by
  obtain ⟨k₁, hk₁, c₁, h₁⟩ := xp_den (x : E)
  obtain ⟨k₂, hk₂, c₂, h₂⟩ := xp_den ((x⁻¹ : Eˣ) : E)
  refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, (k₂ : 𝓞 E) * (c₁ - k₁), (k₁ : 𝓞 E) * (c₂ - k₂), ?_, ?_⟩
  · have h := h₁
    push_cast at h ⊢
    linear_combination (k₂ : E) * h
  · have h := h₂
    push_cast at h ⊢
    linear_combination (k₁ : E) * h

variable (F) in
theorem xp_T_finite (M : ℕ) (hM : 0 < M) : {v : HeightOneSpectrum (𝓞 F) | ((M : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((M : ℕ) : 𝓞 F)} ≠ (0 : Ideal (𝓞 F)) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.2 hv

theorem twist_product_formula : XiProd := by
  intro F E _ _ _ _ _ L _ S ξ x
  obtain ⟨⟨hrat, ⟨N, hN, hcong⟩, _⟩, -⟩ := (mem_tupGrp (ξ : Chr F E L)).mp ξ.2
  obtain ⟨k, hk, b, b', hb, hb'⟩ := unit_sub_one_bounded_denominator x
  have hM : 0 < N * k := Nat.mul_pos hN hk
  set T : Finset (HeightOneSpectrum (𝓞 F)) := (xp_T_finite F (N * k) hM).toFinset with hTdef
  have hmemT : ∀ v, v ∈ T ↔ ((N * k : ℕ) : 𝓞 F) ∈ v.asIdeal := fun v => by
    rw [hTdef, Set.Finite.mem_toFinset]; rfl
  have hloc : ∀ v, v ∉ T → lamX (ξ : Chr F E L) v x = 1 := by
    intro v hv
    obtain ⟨g, hg, hd⟩ := xp_g (N * k) hM (Formalism.L2.G.sgl F v 1) (qu_sgl_int v 1 (one_mem _)) (fun w hw => by
      have hwv : w ≠ v := fun h => hv ((hmemT v).2 (h ▸ hw))
      exact Formalism.L2.G.sgl_apply_ne F v 1 hwv)
    have hdd : Formalism.L2.G.sgl F v 1 * Formalism.L2.G.sgl F v 1 = Formalism.L2.G.sgl F v 1 := by rw [← Formalism.L2.G.sgl_mul, one_mul]
    exact hcong (xp_mem_congN N k x b b' hb hb' g hg _ hd hdd (locId E v x) rfl)
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => lamX (ξ : Chr F E L) v x) ⊆ (T : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    by_contra h
    exact hv (hloc v h)
  refine ⟨T.finite_toSet.subset hsupp, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  have e1 : (∏ v ∈ T, lamX (ξ : Chr F E L) v x) = (ξ : Chr F E L) (∏ v ∈ T, locId E v x) := by
    rw [map_prod]; rfl
  rw [e1]
  let U : (AfE F E)ˣ :=
    { val := xpJ (1 - xpE T) (x : E)
      inv := xpJ (1 - xpE T) ((x⁻¹ : Eˣ) : E)
      val_inv := by rw [xp_J_same (xp_E_compl_idem T), Units.mul_inv, xp_J_at_one]
      inv_val := by rw [xp_J_same (xp_E_compl_idem T), Units.inv_mul, xp_J_at_one] }
  have hU : (ξ : Chr F E L) U = 1 := by
    obtain ⟨g, hg, hd⟩ := xp_g (N * k) hM (1 - xpE T) (Subring.sub_mem _ (Subring.one_mem _) (xp_E_int T)) (fun w hw => by
      classical
      rw [map_sub, map_one, xp_E_at, if_pos ((hmemT w).2 hw), sub_self])
    exact hcong (xp_mem_congN N k x b b' hb hb' g hg _ hd (xp_E_compl_idem T) U rfl)
  have hprod : (∏ v ∈ T, locId E v x) * U = ratId F E x := by
    apply Units.ext
    rw [Units.val_mul, xp_prod]
    show xpJ (xpE T) (x : E) * xpJ (1 - xpE T) (x : E) = _
    rw [xp_J_orth (xp_E_orth T), add_sub_cancel, xp_J_one]
    rfl
  have hr : (ξ : Chr F E L) (ratId F E x) = 1 := hrat ⟨x, rfl⟩
  rw [← hprod, map_mul, hU, mul_one] at hr
  exact hr

end XP

end Formalism.L2.Ker
end
end

