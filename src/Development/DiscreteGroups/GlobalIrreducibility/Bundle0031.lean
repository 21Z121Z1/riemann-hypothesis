import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0026
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0010
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0029
import Formalism.ConjugateSelfDual.Statement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0028

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzLCusp
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.LocLanglands
open scoped Classical

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem twKer_twoBlocks_eq_top (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n a : ℕ} (h0 : 0 < a) (ha : a < n)
    (τ : FDRep ℂ (Gn g n)) (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 = ⊤ := by
  obtain ⟨φ, hφ0, hφ⟩ := hs
  have hgen : ∀ x : GL (Fin n) k, x ∈ GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) → ∀ v,
      σ.ρ x v - v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro x hx v
    refine Submodule.subset_span ⟨⟨x, hx⟩, v, ?_⟩
    simp
  have hφT : ∀ w, φ w ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro w
    have hfin := sum_unip_eq_zero τ hτ h0 ha
    have key : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        φ w - φ (τ.ρ (u : Gn g n) w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
      intro u
      obtain ⟨κ, hred, hmem⟩ := exists_lift i (u : Gn g n) u.2
      have h1 := hφ κ w
      rw [hred] at h1
      rw [h1, ← neg_sub]
      exact Submodule.neg_mem _ (hgen _ hmem (φ w))
    have hsum : ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        (φ w - φ (τ.ρ (u : Gn g n) w)) =
          (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) • φ w := by
      rw [Finset.sum_sub_distrib, ← map_sum φ (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n) w),
        ← LinearMap.sum_apply Finset.univ
          (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n)) w, hfin, LinearMap.zero_apply, map_zero,
        sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    have hc : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hmem := Submodule.sum_mem _ fun u (_ : u ∈ Finset.univ) => key u
    rw [hsum] at hmem
    have := Submodule.smul_mem _
      (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hall : ∀ (h : GL (Fin n) k) (w : τ),
      σ.ρ h (φ w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro h w
    obtain ⟨p, hp, k0, hk0, rfl⟩ :=
      GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL k n (monotone_twoBlocks (N := n) a) h
    obtain ⟨κ, rfl⟩ := exists_inc_eq i hi k0 hk0
    rw [map_mul, Module.End.mul_apply]
    refine twKer_le_comap σ.ρ _ p (blockUpper_le_normalizer (GlobalTheory.FiniteGL.twoBlocks n a) hp) ?_
    have h1 := hφ κ w
    rw [show (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g n κ) (φ w) =
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ)) (φ w) from rfl] at h1
    rw [← h1]
    exact hφT _
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (LinearMap.ext hcon)
  let S : Subrepresentation σ.ρ :=
    ⟨Submodule.span ℂ {v | ∃ (h : GL (Fin n) k) (w : τ), v = σ.ρ h (φ w)}, fun x v hv => by
      refine (Submodule.span_le.2 ?_ : _ ≤ (Submodule.span ℂ _).comap (σ.ρ x)) hv
      rintro _ ⟨h, w, rfl⟩
      exact Submodule.subset_span ⟨x * h, w, by rw [map_mul, Module.End.mul_apply]⟩⟩
  have hST : S.toSubmodule ≤ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 :=
    Submodule.span_le.2 (by rintro _ ⟨h, w, rfl⟩; exact hall h w)
  have hirr := σ.irr
  rcases eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hm : φ w0 ∈ S.toSubmodule := Submodule.subset_span ⟨1, w0, by rw [map_one, Module.End.one_apply]⟩
    rw [hS] at hm
    exact hw0 ((Submodule.mem_bot ℂ).1 hm)
  · refine eq_top_iff.2 fun v _ => hST ?_
    rw [hS]
    trivial

theorem isCuspidal_of_inflates (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (τ : FDRep ℂ (Gn g n))
    (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    IsCuspidal σ.ρ := by
  refine ⟨σ.smooth, fun s d e he => ?_⟩
  obtain ⟨Q, a, h0, ha, hQ⟩ := exists_perm_conj e he
  have htop := twKer_twoBlocks_eq_top i hi h0 ha τ hτ σ hs
  have hinvQ : ∀ z, σ.ρ Q⁻¹ (σ.ρ Q z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hmap : twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 ≤
      (twKer σ.ρ (unipRad k e) 1).comap (σ.ρ Q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, y, rfl⟩
    refine Submodule.subset_span ⟨⟨Q * x * Q⁻¹, hQ x hx⟩, σ.ρ Q y, ?_⟩
    simp [map_mul, Module.End.mul_apply, hinvQ]
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have hv : σ.ρ Q⁻¹ v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    rw [htop]
    exact Submodule.mem_top
  have := hmap hv
  rwa [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at this

end DiscreteGroups.sglob.DzLc

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lCusp : LCusp := by
  intro E _ _ w g _ i hi n hn τ hτ σ hs
  exact GlobalTheory.LocGL.IrrGL.isCusp_of.2 ⟨hn, DiscreteGroups.sglob.DzLc.isCuspidal_of_inflates i hi τ hτ σ hs⟩

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzNormV
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Filter Topology

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem val_lt_one_of_norm_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (u : ℚ_[g])
    (hu : ‖u‖ < 1) : Valued.v (i u) < 1 := by
  have := DiscreteGroups.sglob.DzIso.norm_lt_of_lt i hi hu
  rwa [Valued.toNormedField.norm_lt_one_iff] at this

theorem mem_of_val_lt_one (y : 𝓞 E) (h : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) < 1) :
    y ∈ w.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rwa [e] at h

theorem val_le_one_int (y : 𝓞 E) : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≤ 1 := by
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rw [e]
  exact w.valuation_le_one y

theorem alg_sub_natCast (y : 𝓞 E) (a : ℕ) : algebraMap E (w.adicCompletion E) (((y - (a : 𝓞 E) : 𝓞 E)) : E) =
    algebraMap E (w.adicCompletion E) (y : E) - (a : w.adicCompletion E) := by
  simp

theorem alg_natCast (a : ℕ) : algebraMap E (w.adicCompletion E) (((a : 𝓞 E)) : E) = (a : w.adicCompletion E) := by
  simp

theorem normV_eq_of_padic (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g := by
  classical
  have hres : ∀ y : 𝓞 E, ∃ a : ℕ, y - (a : 𝓞 E) ∈ w.asIdeal := by
    intro y
    set x := i.symm (algebraMap E (w.adicCompletion E) (y : E)) with hx
    have hxy : i x = algebraMap E (w.adicCompletion E) (y : E) := by rw [hx, RingEquiv.apply_symm_apply]
    have hxn : ‖x‖ ≤ 1 := by
      by_contra hc
      push Not at hc
      have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact absurd hc (by norm_num)
      have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
      have h2 := val_lt_one_of_norm_lt_one w g i hi _ h1
      rw [map_inv₀, hxy, map_inv₀] at h2
      have h3 := val_le_one_int w y
      have hy0 : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≠ 0 := by
        intro h0
        rw [h0, inv_zero] at h2
        have : i x ≠ 0 := (map_ne_zero i).mpr hx0
        rw [hxy] at this
        exact this ((Valuation.zero_iff _).mp h0)
      have h4 : 1 ≤ (Valued.v (algebraMap E (w.adicCompletion E) (y : E)))⁻¹ := one_le_inv₀ (zero_lt_iff.mpr hy0) |>.mpr h3
      exact absurd h2 (not_lt.mpr h4)
    let xz : ℤ_[g] := ⟨x, hxn⟩
    obtain ⟨a, -, ha⟩ := PadicInt.exists_mem_range xz
    refine ⟨a, mem_of_val_lt_one w _ ?_⟩
    have h5 : ‖x - a‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp ha
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hxy, map_natCast] at h6
    rw [alg_sub_natCast]
    exact h6
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    apply mem_of_val_lt_one w
    have := val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
    rw [map_natCast] at this
    rw [alg_natCast]
    exact this
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hgQ : ((g : ℕ) : 𝓞 E ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hgw
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := (CharP.charP_iff_prime_eq_zero hg.out).mpr hgQ
  let f : ZMod g →+* 𝓞 E ⧸ w.asIdeal := ZMod.castHom (dvd_refl g) _
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := hres y
    refine ⟨(a : ZMod g), ?_⟩
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_refl g), ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact ha
  unfold normV
  rw [← Nat.card_congr (RingEquiv.ofBijective f ⟨hinj, hsurj⟩).toEquiv, Nat.card_zmod]

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzRedSupp
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Conj

variable {F : Type} [Field F] {n : ℕ}

theorem conj_apply (δ : Fin n → Fˣ) (u : GL (Fin n) F) (a b : Fin n) :
    ((Iwasawa.diagGL F n δ * u * (Iwasawa.diagGL F n δ)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      (δ a : F) * (u : Matrix (Fin n) (Fin n) F) a b * (δ b : F)⁻¹ := by
  rw [show (Iwasawa.diagGL F n δ)⁻¹ = Iwasawa.diagGL F n δ⁻¹ from (map_inv _ _).symm, Units.val_mul,
    Units.val_mul, Iwasawa.coe_diagGL, Iwasawa.coe_diagGL, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

theorem conj_mem_unipB (δ : Fin n → Fˣ) {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) :
    Iwasawa.diagGL F n δ * u * (Iwasawa.diagGL F n δ)⁻¹ ∈ unipB F (Fin n) := by
  rw [mem_unipB] at hu ⊢
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [conj_apply, hu.1 a b hab]; simp
  · rw [conj_apply, hu.2 a]; simp

theorem superDiag_conj (δ : Fin n → Fˣ) (u : GL (Fin n) F) :
    superDiag (Iwasawa.diagGL F n δ * u * (Iwasawa.diagGL F n δ)⁻¹) =
      ∑ a : Fin n, ∑ b : Fin n with b.val = a.val + 1,
        (δ a : F) * (u : Matrix (Fin n) (Fin n) F) a b * (δ b : F)⁻¹ := by
  unfold superDiag
  simp_rw [conj_apply]

def tv (a b : Fin n) (hab : a ≠ b) (c : F) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection a b c)
    (by rw [Matrix.det_transvection_of_ne a b hab c]; exact one_ne_zero)

theorem tv_apply (a b : Fin n) (hab : a ≠ b) (c : F) (x y : Fin n) :
    (tv a b hab c : Matrix (Fin n) (Fin n) F) x y =
      (1 : Matrix (Fin n) (Fin n) F) x y + if x = a ∧ y = b then c else 0 := by
  show Matrix.transvection a b c x y = _
  by_cases h : x = a ∧ y = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.transvection]
  · simp only [Matrix.transvection, Matrix.add_apply, h, if_false]
    congr 1
    rw [Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

theorem tv_mem_unipB (a b : Fin n) (hab : a < b) (c : F) : tv a b hab.ne c ∈ unipB F (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · rw [tv_apply, Matrix.one_apply_ne (ne_of_gt hxy)]
    have : ¬ (x = a ∧ y = b) := by rintro ⟨rfl, rfl⟩; exact absurd (hxy.trans hab) (lt_irrefl _)
    simp [this]
  · rw [tv_apply, Matrix.one_apply_eq]
    have : ¬ (x = a ∧ x = b) := by rintro ⟨rfl, h⟩; exact hab.ne h
    simp [this]

theorem conj_tv (δ : Fin n → Fˣ) (a b : Fin n) (hab : a ≠ b) (c : F) :
    Iwasawa.diagGL F n δ * tv a b hab c * (Iwasawa.diagGL F n δ)⁻¹ = tv a b hab ((δ a : F) * c * (δ b : F)⁻¹) := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  rw [conj_apply, tv_apply, tv_apply]
  by_cases hxy : x = y
  · subst hxy
    have : ¬ (x = a ∧ x = b) := by rintro ⟨rfl, h⟩; exact hab h
    simp [this]
  · rw [Matrix.one_apply_ne hxy]
    by_cases h : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp [h]

theorem superDiag_tv (a b : Fin n) (hb : b.val = a.val + 1) (c : F) :
    superDiag (tv a b (fun h => by rw [h] at hb; omega) c) = c := by
  unfold superDiag
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [tv_apply, Matrix.one_apply_ne (fun h => by rw [h] at hb; omega)]; simp
    · intro y _ hy
      rw [tv_apply, Matrix.one_apply_ne (fun h => by subst h; simp_all)]
      simp [hy]
    · intro h; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ b, hb⟩) h
  · intro x _ hx
    refine Finset.sum_eq_zero fun y hy => ?_
    have hy' := (Finset.mem_filter.1 hy).2
    rw [tv_apply, Matrix.one_apply_ne (fun h => by subst h; omega)]
    simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

end Conj

end DiscreteGroups.sglob.DzRed
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LongEltCornerEqCyc
section
noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

theorem longElt_corner_eq_cyc (m : ℕ) :
    longElt (m + 1) (ZMod g) * corner (longElt m (ZMod g)) = cyc g (m + 1) := by
  apply Units.ext
  ext i k
  rw [Units.val_mul, DzRed.longElt_mul_apply]
  show _ = if i = finRotate (m + 1) k then (1 : ZMod g) else 0
  have hrv : ((Fin.rev i : Fin (m + 1)) : ℕ) = m - i := by rw [Fin.val_rev]; omega
  have hil := i.isLt
  rcases Fin.eq_castSucc_or_eq_last (Fin.rev i) with ⟨d, hd⟩ | hd
  · rw [hd]
    have hdv : (d : ℕ) = m - i := by rw [← hrv, hd, Fin.coe_castSucc]
    have hdl := d.isLt
    rcases Fin.eq_castSucc_or_eq_last k with ⟨c, rfl⟩ | rfl
    · rw [DzRed.corner_cs_cs, DzRed.val_longElt]
      have hc : ((finRotate (m + 1) c.castSucc : Fin (m + 1)) : ℕ) = c + 1 := by
        rw [finRotate_succ_apply, Fin.val_add_one, if_neg (Fin.castSucc_lt_last c).ne, Fin.coe_castSucc]
      have hcl := c.isLt
      by_cases h : c = d.rev
      · rw [if_pos h, if_pos]
        ext
        rw [hc]
        have := congrArg Fin.val h
        rw [Fin.val_rev] at this
        omega
      · rw [if_neg h, if_neg]
        intro e
        apply h
        ext
        have := congrArg Fin.val e
        rw [hc] at this
        rw [Fin.val_rev]
        omega
    · rw [DzRed.corner_cs_last, if_neg]
      intro e
      have := congrArg Fin.val e
      rw [finRotate_succ_apply, Fin.last_add_one, Fin.val_zero] at this
      omega
  · rw [hd]
    have hi0 : (i : ℕ) = 0 := by
      have := congrArg Fin.val hd
      rw [hrv, Fin.val_last] at this
      omega
    rcases Fin.eq_castSucc_or_eq_last k with ⟨c, rfl⟩ | rfl
    · rw [DzRed.corner_last_cs, if_neg]
      intro e
      have := congrArg Fin.val e
      rw [finRotate_succ_apply, Fin.val_add_one, if_neg (Fin.castSucc_lt_last c).ne, Fin.coe_castSucc] at this
      omega
    · rw [DzRed.corner_last_last, if_pos]
      ext
      rw [finRotate_succ_apply, Fin.last_add_one, Fin.val_zero, hi0]

theorem exists_corner [Fact g.Prime] {m : ℕ} (M : GL (Fin (m + 1)) (ZMod g))
    (hr : ∀ l, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) (Fin.last m) l = if l = Fin.last m then 1 else 0)
    (hc : ∀ i, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) i (Fin.last m) = if i = Fin.last m then 1 else 0)
    (hlow : ∀ i l : Fin m, i < l → (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) i.castSucc l.castSucc = 0) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = M := by
  have hne : ∀ j : Fin m, j.castSucc ≠ Fin.last m := fun j => (Fin.castSucc_lt_last j).ne
  set A : Matrix (Fin m) (Fin m) (ZMod g) :=
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)).submatrix Fin.castSucc Fin.castSucc with hA
  have he : ((-1 : ZMod g) ^ (m + m)) = 1 := by rw [← two_mul, pow_mul]; simp
  have hdet : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)).det = A.det := by
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    simp [hr, hne, Fin.succAbove_last, A, he]
  have hAd : A.det ≠ 0 := by
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAd, fun i l hil => hlow i l hil, ?_⟩
  apply Units.ext
  ext i l
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last l with ⟨l, rfl⟩ | rfl
  · rw [DzRed.corner_cs_cs]; rfl
  · rw [DzRed.corner_cs_last, hc, if_neg (hne i)]
  · rw [DzRed.corner_last_cs, hr, if_neg (hne l)]
  · rw [DzRed.corner_last_last, hr, if_pos rfl]

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.TopLeftElemInv
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {p : Fin n} (hp : p.val < j) (hne : p ≠ i0 j hj hj1)
include hp

theorem topLeft_single (y : k) (i l : Fin n) (h : j ≤ i.val ∨ j ≤ l.val) :
    Matrix.single p (i0 j hj hj1) y i l = 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  omega

theorem topLeft_elem (y : k) : TopLeft j ((GlobalTheory.RootUp.elem hne y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [GlobalTheory.RootUp.val_elem, Matrix.add_apply, topLeft_single j hj hj1 hp y i l h, add_zero]

theorem topLeft_elem_inv (y : k) :
    TopLeft j (((GlobalTheory.RootUp.elem hne y)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - Matrix.single p (i0 j hj hj1) y) i l = _
  rw [Matrix.sub_apply, topLeft_single j hj hj1 hp y i l h, sub_zero]

theorem rowMul_elem_inv (ξ : Fin n → k) :
    rowMul j ξ (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (i0 j hj hj1) =
      ξ (i0 j hj hj1) + ξ p := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i (i0 j hj hj1) else 0) =
      (if i = i0 j hj hj1 then ξ (i0 j hj hj1) else 0) + (if i = p then ξ p else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - Matrix.single p (i0 j hj hj1) (-1 : k)) i (i0 j hj hj1) else 0) = _
    rw [Matrix.sub_apply, Matrix.single_apply, one_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi]
      by_cases h1 : i = i0 j hj hj1
      · subst h1
        have : ¬ (p = i0 j hj hj1) := hne
        simp [this, Ne.symm hne]
      · by_cases h2 : i = p
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact hi0)), if_neg (fun e => hi (by rw [e]; exact hp)),
        add_zero]
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

end DiscreteGroups.sglob.LConvGenM
end
end

