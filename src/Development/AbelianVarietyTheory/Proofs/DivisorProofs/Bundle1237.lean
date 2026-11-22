import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0409
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPtLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fstA (E : Type) [Field E] [NumberField E] : Ad E →+* InfiniteAdeleRing E := RingHom.fst _ _

theorem fst_entry (γ : GL (Fin n) E) (i j : Fin n) :
    fstA E ((finGL E n (ratF E n γ)).val i j) = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).1 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem snd_entry (γ : GL (Fin n) E) (i j : Fin n) :
    pFin E ((finGL E n (ratF E n γ)).val i j) = algebraMap E (Af E) (γ.val i j) := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).2 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (M : Matrix (Fin n) (Fin n) A) : (cT σ M).map f = cT τ (M.map f) := by
  ext i j; simp [cT, h]

theorem ext_ad (M N : Matrix (Fin n) (Fin n) (Ad E)) (h1 : M.map (fstA E) = N.map (fstA E))
    (h2 : M.map (pFin E) = N.map (pFin E)) : M = N := by
  ext i j
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem mem_UA (γ : UE E n) : finGL E n (ratF E n γ.1) ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  show cT (conjAd E) (finGL E n (ratF E n γ.1)).val * 1 * (finGL E n (ratF E n γ.1)).val = 1
  have hf : (finGL E n (ratF E n γ.1)).val.map (fstA E) = 1 := by
    ext i j; rw [Matrix.map_apply, fst_entry]
  have hs : (finGL E n (ratF E n γ.1)).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
    ext i j; rw [Matrix.map_apply, snd_entry]; rfl
  apply ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (fstA E) (conjAd E) ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j; simp [cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (pFin E) (conjAd E) (conjFin (IsCMField.complexConj E).toRingEquiv) (fun x => rfl), hs,
      Matrix.map_one _ (map_zero _) (map_one _)]
    have : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.1.val.map (algebraMap E (Af E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val).map (algebraMap E (Af E)) := by
      ext i j; simp [cT, conjFin_algebraMap]
    rw [this, ← Matrix.map_one (algebraMap E (Af E)) (map_zero _) (map_one _), ← Matrix.map_mul, ← Matrix.map_mul, hγ]

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (h : g ∈ H) : toSub H g = ⟨g, h⟩ :=
  dif_pos h

theorem mem_finU (γ : UE E n) : (⟨_, mem_UA γ⟩ : UA E n) ∈ finU E n := by
  show cInf (⟨_, mem_UA γ⟩ : UA E n) = 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (infEq E).symm (fstA E ((finGL E n (ratF E n γ.1)).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j
  rw [fst_entry]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem finPt_eq (γ : UE E n) : ((finPt γ : finU E n) : UA E n) = ⟨_, mem_UA γ⟩ := by
  have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, mem_UA γ⟩ := toSub_of_mem _ _ (mem_UA γ)
  unfold finPt
  rw [h1, toSub_of_mem _ _ (mem_finU γ)]

end GlobalTheory.BCT.FinPtLoc

theorem GlobalTheory.BCT.locPt_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    toSub (UL n w) (cLoc w ((finPt γ : finU E n) : UA E n)) = locPt w γ := by
  intro E _ _ _ _ n γ w
  rw [FinPtLoc.finPt_eq]
  unfold locPt
  congr 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Topology ValuativeRel

namespace GlobalTheory.CjInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}

theorem valuation_equiv :
    (valuation (w.adicCompletion E)).IsEquiv (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv _ _

theorem lt_one_iff (x : w.adicCompletion E) : valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  simp only [← not_le]
  exact not_congr valuation_equiv.one_le_iff_one_le

theorem tendsto_pow_zero {x : w.adicCompletion E} (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [← lt_one_iff] at h
  rw [(IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero (w.adicCompletion E)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  show valuation _ (x ^ m) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) := by
  have := (IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩
  simpa only [lt_one_iff] using this

theorem lt_one_of_map (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) {x : w.adicCompletion E}
    (h : Valued.v x < 1) : Valued.v (s x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s x ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ Valued.v (s x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem valued_map_eq (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) (hss : ∀ x, s (s x) = x)
    (x : w.adicCompletion E) : Valued.v (s x) = Valued.v x := by

  have hle : ∀ y : w.adicCompletion E, Valued.v y ≤ 1 → Valued.v (s y) ≤ 1 := by
    intro y hy
    by_contra hc
    push_neg at hc
    have hy0 : s y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hc; exact absurd hc (not_lt.2 zero_le')
    have h1 : Valued.v (s y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := lt_one_of_map s hs h1
    rw [map_inv₀, hss, map_inv₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]
      intro h; apply hy0; rw [h, map_zero]
    exact absurd hy (not_le.2 ((inv_lt_one₀ h0).1 h2))

  have hord : ∀ a b : w.adicCompletion E, b ≠ 0 → Valued.v a ≤ Valued.v b → Valued.v (s a) ≤ Valued.v (s b) := by
    intro a b hb hab
    have hb' : s b ≠ 0 := (map_ne_zero s).2 hb
    have h1 : Valued.v (a / b) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le'
    have h2 := hle _ h1
    rw [map_div₀, map_div₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s b) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact hb'
    exact (div_le_one₀ h0).1 h2

  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  set p : w.adicCompletion E := algebraMap E (w.adicCompletion E) π with hp
  have hvp : Valued.v p = WithZero.exp (-1) := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
    rw [hπ] at this
    exact this
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hvp; exact WithZero.exp_ne_zero hvp.symm
  have hsp0 : s p ≠ 0 := (map_ne_zero s).2 hp0
  have hvsp : Valued.v (s p) = Valued.v p := by
    apply le_antisymm
    · rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    · have := hord (s p) p hp0 (by
        rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
      rwa [hss] at this
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  set k := WithZero.log (Valued.v x) with hk
  set u := x * p ^ k with hu
  have hvpk : Valued.v p ^ k ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hp0)
  have hvu : Valued.v u = 1 := by
    rw [hu, map_mul, map_zpow₀, hvp, ← WithZero.exp_log hvx, ← hk, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hsu1 : Valued.v (s u) ≤ 1 := hle u hvu.le
  have hsu2 : Valued.v (s u⁻¹) ≤ 1 := hle u⁻¹ (by rw [map_inv₀, hvu, inv_one])
  have hsu : Valued.v (s u) = 1 := by
    apply le_antisymm hsu1
    rw [map_inv₀, map_inv₀] at hsu2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s u) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero s).2 hu0
    exact (inv_le_one₀ h0).1 hsu2
  rw [hu, map_mul, map_zpow₀, map_mul, map_zpow₀, hvsp] at hsu
  rw [hu, map_mul, map_zpow₀] at hvu
  exact mul_right_cancel₀ hvpk (hsu.trans hvu.symm)

end GlobalTheory.CjInv

namespace GlobalTheory.BCT

theorem cj_involutive_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  intro E _ _ _ w
  have key : (∀ x, cj w (cj w x) = x) ∧ Continuous (cj w) := by
    unfold cj
    split_ifs with h
    · obtain ⟨hc, hE⟩ := h.choose_spec
      refine ⟨fun x => ?_, hc⟩
      have hd := HeightOneSpectrum.denseRange_algebraMap E w
      have := hd.equalizer (hc.comp hc) continuous_id (funext fun y => by
        simp only [Function.comp_apply, id_eq, hE, IsCMField.complexConj_apply_apply])
      exact congrFun this x
    · exact ⟨fun x => rfl, continuous_id⟩
  exact ⟨key.1, GlobalTheory.CjInv.valued_map_eq (cj w) key.2 key.1⟩

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompat
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeomFrobChar

open GlobalTheory.WeilDeligne Polynomial in

theorem charpoly_geomFrob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  intro E Ω _ _ _ _ _ l _ ι a r hr w hl B h rc hrc σ S hS t hw g hg
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := ParLaws.rec_eq_diag hrc (σ := ParLaws.toRep σ) hα
  let φ : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
  have hφ : deg φ = 1 := deg_eq_one_iff.mpr hg
  have h1 := charPol_wdOf hl ι (Units.continuous_val.comp hr) φ⁻¹
  have e' : rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  have h2 : ((WDRep.diag h fun i => (α i)⁻¹).tw t).ρ φ⁻¹ =
      diagEnd fun i => (α i : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.tw_ρ, WDRep.diag_ρ, deg_inv, hφ, Complex.ofReal_neg, Complex.cpow_neg]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply, mul_assoc, mul_left_comm]
  rw [hw, e', WD.lpTw_mk, WD.charPol_mk, h2, charpoly_diagEnd] at h1
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [zpow_neg_one]
  refine (show _ = _ from h1.symm).trans ?_
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp

end GlobalTheory.GeomFrobChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignFullCharpolyEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.KapSignFull

theorem ordL_cj_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (hcj : ∀ x, Valued.v (cj w x) = Valued.v x) (x : w.adicCompletion E) (hx : x ≠ 0) :
    ordL (cj w x * x) = 2 * ordL x := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  have e : Valued.v (cj w x * x) = Valued.v x * Valued.v x := by rw [map_mul, hcj]
  have h1 : Valued.v (cj w x * x) ≠ 0 := by rw [e]; exact mul_ne_zero h0 h0
  unfold ordL
  rw [dif_neg h1, dif_neg h0]
  have : WithZero.unzero h1 = WithZero.unzero h0 * WithZero.unzero h0 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, e]
  rw [this, toAdd_mul]; ring

theorem kapSign_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  intro E _ _ _ n w hcj γ
  unfold kapSign
  split_ifs with hs
  · rfl
  · simp only []
    set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val γ.val.charpoly)) with hV
    have htop : V₁ = ⊤ := by rw [hV, Matrix.aeval_self_charpoly]; simp
    set b := Module.finBasis (w.adicCompletion E) V₁
    have hm : Module.finrank (w.adicCompletion E) V₁ = n := by
      rw [htop, finrank_top]; simp
    let e : Fin (Module.finrank (w.adicCompletion E) V₁) ≃ Fin n := finCongr hm
    let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := fun k j => (b (e.symm j)).1 k
    have hG : (Matrix.of fun i j => ∑ k, cj w ((b i).1 k) * (b j).1 k) =
        ((M.map (cj w))ᵀ * M).submatrix e e := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => rfl
    have hM : M.det ≠ 0 := by
      have hli : LinearIndependent (w.adicCompletion E) M.col := by
        have h1 : LinearIndependent (w.adicCompletion E) (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) :=
          b.linearIndependent.map' V₁.subtype (Submodule.ker_subtype V₁)
        have h2 := h1.comp e.symm e.symm.injective
        have hc : M.col = (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) ∘ e.symm := by funext j; rfl
        rw [hc]; exact h2
      exact (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli) |>.ne_zero
    rw [hG, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, show (M.map (cj w)).det = cj w M.det by rw [RingHom.map_det]; rfl,
      ordL_cj_mul w hcj _ hM]
    exact Even.neg_one_zpow ⟨ordL M.det, by ring⟩

end GlobalTheory.BCT.KapSignFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 → 0 < m → IsLogEqn p Γ η x m g → (LcAt p n Γ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g) := by
  first | exact @GlobalTheory.PairStep.lcAt_iff_of_isLogEqn | exact GlobalTheory.PairStep.lcAt_iff_of_isLogEqn | (intros; apply GlobalTheory.PairStep.lcAt_iff_of_isLogEqn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatGoodOfBlockExtensionTwist
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FullRankSum

theorem joint_inj {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L] {a b c : ℕ}
    (B : Mx O a c) (C : Mx O b c) (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) (x : Fin c → L)
    (hB : (B.map (algebraMap O L)).mulVec x = 0) (hC : (C.map (algebraMap O L)).mulVec x = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6; revert O L h_2 h_3 h_4 h_5 h_6 a b c B C h x hB hC; exact @_root_.GlobalTheory.MulVecZeroDenominator.target)
  | exact @_root_.GlobalTheory.MulVecZeroDenominator.target
  | exact _root_.GlobalTheory.MulVecZeroDenominator.target
  | (apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulVecZeroDenominator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulVecZeroDenominator.target ..)

theorem exists_equiv {L : Type} [Field L] {n : ℕ} (B : Mx L n (n + 1)) (C : Mx L 1 (n + 1))
    (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) :
    ∃ e : (Fin (n + 1) → L) ≃ₗ[L] (Fin n → L) × (Fin 1 → L), ∀ v, e v = (B.mulVec v, C.mulVec v) := by
  let φ : (Fin (n + 1) → L) →ₗ[L] (Fin n → L) × (Fin 1 → L) := (Matrix.toLin' B).prod (Matrix.toLin' C)
  have hi : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h v (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  exact ⟨φ.linearEquivOfInjective hi (by simp), fun v => rfl⟩

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l}

theorem tw_mulVec {a b : ℕ} {r : ↥(GK K) →* GL (Fin b) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin a) ↥(OL LL)}
    {A : Mx ↥(OL LL) a b} (hA : Tw r r' A) (g : ↥(GK K)) (y : Fin b → ↥LL.1) :
    (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (repOf r g y) =
      repOf r' g ((A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec y) := by
  rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
    hA g]

theorem matGood_sum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  intro l _ P AI T K LL f n emb r ρ r₂ U U' B C hr hρ hB hC hinj
  obtain ⟨_, -, -, -, -, -, hF⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨e, he⟩ := exists_equiv (B.map (algebraMap ↥(OL LL) ↥LL.1)) (C.map (algebraMap ↥(OL LL) ↥LL.1))
    (joint_inj B C hinj)
  have hq : ∀ g v, e (repOf r₂ g v) = (repOf r g (e v).1, repOf ρ g (e v).2) := fun g v => by
    rw [he, he, tw_mulVec hB, tw_mulVec hC]
  obtain ⟨-, hc, hm⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T K LL _ (repOf r₂) _ (repOf r) _ (repOf ρ) e hq
  refine ⟨fun a b => ?_, hc.2 ⟨hr.2.1, hρ.2.1⟩, fun i τ hτ a => ?_⟩
  · have c1 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _) := LinearMap.continuous_on_pi _
    have c2 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _) := LinearMap.continuous_on_pi _
    have d1 : Continuous fun g => repOf r g (e (Pi.single b 1)).1 := (latOf r hr.1).cont _
    have d2 : Continuous fun g => repOf ρ g (e (Pi.single b 1)).2 := (latOf ρ hρ.1).cont _
    have d := (continuous_apply a).comp ((c1.comp d1).add (c2.comp d2))
    refine d.congr fun g => ?_
    have : repOf r₂ g (Pi.single b 1) = e.symm (repOf r g (e (Pi.single b 1)).1, 0) +
        e.symm (0, repOf ρ g (e (Pi.single b 1)).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, ← hq, e.symm_apply_apply]
    have h2 := congrFun this a
    rw [repOf_apply, Matrix.mulVec_single_one] at h2
    exact h2.symm
  · rw [hm, hr.2.2 i τ hτ a, hρ.2.2 i τ hτ a, Multiset.count_add]
    push_cast
    rfl

end GlobalTheory.WachPlace.FullRankSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLineStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_fibre_product_stable_lattice_chain_line : ∀ {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (Ac As : Matrix (Fin n) (Fin n) O) (ρc ρs : Γ →* GL (Fin n) O) (x : Fin n → O), Function.Injective Ac.mulVec → Function.Injective As.mulVec → Tw ρc r Ac → Tw ρs r As → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (∀ g, ∃ u, Ac *ᵥ u = (r g : Matrix (Fin n) (Fin n) O) *ᵥ x - fun a => (χ g : O) * x a) → ∃ (r2 : Γ →* GL (Fin (n + 1)) O) (B B' : Matrix (Fin n) (Fin (n + 1)) O) (C : Matrix (Fin 1) (Fin (n + 1)) O) (E : Matrix (Fin (n + 1)) (Fin n) O), Tw r2 r B ∧ Tw r2 ρs B' ∧ Tw r2 (GlobalTheory.TripleGal.rk1 χ) C ∧ Tw ρc r2 E ∧ B * E = Ac ∧ C * E = 0 ∧ B = As * B' ∧ (E.map (residue O)).rank = n ∧ (C.map (residue O)).rank = 1 ∧ (B'.map (residue O)).rank = n ∧ ∀ v, B *ᵥ v = 0 → C *ᵥ v = 0 → v = 0 := by
  first | exact @GlobalTheory.FibreLine.fibre_line | exact GlobalTheory.FibreLine.fibre_line | (intros; apply GlobalTheory.FibreLine.fibre_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.RatFix

theorem ratfix_mul_eq (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E) (hBA : B₀ * A₀ = 1) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hG : ∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) :
    G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  set ι : E →+* R ⊗[F] E := inclR (F := F) R with hι
  have hN : (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) - A₀.map ι * B₀.map ι = (1 - A₀ * B₀).map ι := by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
  rw [hN]
  have hBN : B₀ * (1 - A₀ * B₀) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  ext i j
  have hv : B₀.mulVec (fun k => ((1 : Matrix (Fin M) (Fin M) E) - A₀ * B₀) k j) = 0 := by
    funext a
    have := congrFun (congrFun hBN a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have := congrFun (hG _ hv) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem ratfix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) :=
  fun F E _ _ _ R _ _ M A₀ B₀ hBA G hG => ratfix_mul_eq F E R M A₀ B₀ hBA G hG

end GlobalTheory.RatFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma

def intVec (K : UQ) (n : ℕ) : Submodule K.O (Fin n → K.E) where
  carrier := {v | ∀ i, v i ∈ (algebraMap K.O K.E).range}
  add_mem' := fun ha hb i => Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun _ => Subring.zero_mem _
  smul_mem' := fun c v hv i => by
    simp only [Pi.smul_apply, Algebra.smul_def]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv i)

def modelLat {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))
    (P : Matrix (Fin n) (Fin n) K.E) : Submodule K.O B.A :=
  (intVec K n).comap ((Matrix.toLin' P).restrictScalars K.O ∘ₗ ψ.toLinearMap.restrictScalars K.O)

def unitLat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} {K : UQ}
    (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (q : UL n w) :
    Submodule K.O B.A :=
  modelLat B ψ ((((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm)

end GlobalTheory.InertUnitOrb
end
end

