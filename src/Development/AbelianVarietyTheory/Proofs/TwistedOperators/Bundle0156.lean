import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameProd

theorem val_lt_one_of_resS_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (P : Pl E) (g : Formalism.L2.Herm.intAf F E →+* K) (h1 : ∀ s, v (g s) ≤ 1)
    (h2 : ∀ a ∈ P.asIdeal, v (g (oToS F E a)) < 1) (s : Formalism.L2.Herm.intAf F E) (hs : resS F P s = 0) :
    v (g s) < 1 := by
  have hm : s ∈ idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS F P.asIdeal)
      (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 hs
  refine Submodule.span_induction (p := fun s _ => v (g s) < 1) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨a, ha, rfl⟩
    exact h2 a ha
  · rw [map_zero, map_zero]
    exact zero_lt_one
  · intro x y _ _ hx hy
    rw [map_add]
    exact v.map_add_lt hx hy
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (h1 c)).trans_lt hx

theorem val_sub_lt_one {D : D7} {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (P : Pl D.host.E) (G : Af D.host.F ⊗[D.host.F] D.host.E →+* K) (h1 : ∀ y ∈ intAE D, v (G y) ≤ 1)
    (h2 : ∀ a ∈ P.asIdeal, v (G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1) (w : AE D)
    (hw : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (a : 𝓞 D.host.E)
    (h : resS D.host.F P ⟨toEAf D w, hw⟩ = Ideal.Quotient.mk _ a) :
    v (G (finPart D w) - G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
  let g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* K :=
    (G.comp c.symm.toRingEquiv.toRingHom).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have hg : ∀ s, g s = G (c.symm s.1) := fun _ => rfl
  have hgo : ∀ b : 𝓞 D.host.E, g (oToS D.host.F D.host.E b) =
      G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) := fun _ => rfl
  have key := val_lt_one_of_resS_eq_zero v P g
    (fun s => h1 _ ((GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).2 (by
      have : c (c.symm s.1) = s.1 := c.apply_symm_apply _
      exact this.symm ▸ s.2)))
    (fun b hb => by rw [hgo]; exact h2 b hb) (⟨toEAf D w, hw⟩ - oToS D.host.F D.host.E a)
    (by rw [RingHom.map_sub, h, resS_oToS, sub_self])
  rw [RingHom.map_sub, hgo, hg] at key
  have e : c.symm (toEAf D w) = finPart D w := c.symm_apply_apply _
  rwa [e] at key

theorem resS_idem_eq_zero {D : D7} {e : AE D} {P Q : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P) (hQ : P ≠ Q)
    (h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resS D.host.F Q ⟨toEAf D e, h⟩ = 0 := by
  have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
    hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle)).symm
  obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.1 hnle
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxP P.asIdeal.zero_mem
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hi : finPart D (e * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hxP ((he.2 x hx0).2 hn)
  have e1 : (⟨toEAf D e, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨_, GlobalTheory.IdemRes.toEAf_mem_of_finPart hi⟩ * oToS D.host.F D.host.E x := by
    apply Subtype.ext
    change toEAf D e = toEAf D (e * incA D ((x : D.host.E)⁻¹)) * toEAf D (incA D (x : D.host.E))
    rw [← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hx0', RingHom.map_one, mul_one]
  rw [e1, RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hxQ, mul_zero]

theorem map_sum_ringHom {A B ι : Type} [Semiring A] [Semiring B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s

theorem resS_idemSum {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ Q ∈ P, resS D.host.F Q ⟨toEAf D e, h⟩ = 1 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  choose hi hr using fun Q : P => GlobalTheory.IdemRes.resS_idem_eq_one D (es Q) Q (hes Q Q.2)
  let t : P → Formalism.L2.Herm.intAf D.host.F D.host.E := fun Q => ⟨toEAf D (es Q), hi Q⟩
  have ht : toEAf D (∑ PP ∈ P, es PP) = ((∑ Q, t Q : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D) := by
    rw [← Finset.sum_coe_sort P]
    refine (map_sum_ringHom (toEAf D) _ _).trans ?_
    exact (map_sum (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype t Finset.univ).symm
  refine ⟨ht ▸ (∑ Q, t Q).2, fun Q hQ => ?_⟩
  have e1 : (⟨toEAf D (∑ PP ∈ P, es PP), ht ▸ (∑ Q, t Q).2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ Q, t Q :=
    Subtype.ext ht
  rw [e1, map_sum, Finset.sum_eq_single (⟨Q, hQ⟩ : P)]
  · exact hr ⟨Q, hQ⟩
  · intro R _ hR
    exact resS_idem_eq_zero (hes R R.2) (fun h => hR (Subtype.ext h)) _
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem le_exp_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]
    exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem loc_eq_of_tame {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (ht : χ.TameAt Q) (y z : (Q.adicCompletion L)ˣ) (hz : Valued.v (z : Q.adicCompletion L) = 1)
    (h : Valued.v ((y : Q.adicCompletion L) - z) < 1) : χ.loc Q y = χ.loc Q z := by
  have hy : Valued.v (y : Q.adicCompletion L) = 1 := by
    rw [← hz]
    exact Valuation.map_eq_of_sub_lt _ (hz ▸ h)
  have h1 : χ.loc Q (y * z⁻¹) = 1 := by
    refine ht _ ?_ (le_exp_of_lt_one ?_)
    · show Valued.v ((y * z⁻¹ : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = 1
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hz, inv_one, mul_one]
    · have : ((y * z⁻¹ : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) - 1 =
          ((y : Q.adicCompletion L) - z) * (z : Q.adicCompletion L)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ z.ne_zero]
      rw [this, map_mul, map_inv₀, hz, inv_one, mul_one]
      exact h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem tameOn_of_tame : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : AE D) (P : Finset (Pl D.host.E)) (cR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → (∀ PP, χ.TameAt PP) → IsIdemSum e P → (∀ PP, PP ∉ P → (¬ ∃ PP' ∈ P, IsConjPl PP' PP) → χ.UnrAt PP) → (∀ PP ∈ P, IsRes χ PP (cR PP)) → TameOn c e P cR := by
  classical
  intro D c χ e P cR hc ht he hunr hres x hx1 hx2 hx3 hxe u hu
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  let G : ∀ Q : Pl D.host.E, Af D.host.F ⊗[D.host.F] D.host.E →+* Q.adicCompletion D.host.E :=
    fun Q => (GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom
  have hG : ∀ Q y, G Q y = ι y Q := fun _ _ => rfl
  have hG1 : ∀ (Q : Pl D.host.E) (a : D.host.E), G Q ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ a :=
    fun Q a => (congrArg (GlobalTheory.CharLocProd.evalAt Q) (h1 a)).trans (GlobalTheory.CharLocProd.evalAt_algebraMap Q a)
  have hGint : ∀ Q, ∀ y ∈ intAE D, Valued.v (G Q y) ≤ 1 := fun Q y hy => (h2 y).1 hy Q
  have hGlt : ∀ (Q : Pl D.host.E), ∀ a ∈ Q.asIdeal,
      Valued.v (G Q ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1 := by
    intro Q a ha
    rw [hG1, GlobalTheory.CharLocProd.val_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) Q a).2 ha
  have hv : ∀ Q, Valued.v (G Q (finPart D (x : AE D))) = 1 := by
    intro Q
    have a := hGint Q _ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx2)
    have b := hGint Q _ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx3)
    have e' : Valued.v (G Q (finPart D (x : AE D))) * Valued.v (G Q (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) = 1 := by
      rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (G Q (finPart D (x : AE D))) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  choose k hk using fun Q : Pl D.host.E => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN Q
    (G Q (finPart D (x : AE D))) (fun h => by
      have := hv Q
      rw [h, map_zero] at this
      exact zero_ne_one this)
  have hkc : ∀ Q, Valued.v (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (k Q : D.host.E)) < 1 := by
    intro Q
    have b := (hk Q).2.2
    rw [← (hk Q).1, hv, mul_one] at b
    refine b.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hloc : ∀ (Q : Pl D.host.E) (z : D.host.Eˣ), Q.valuation D.host.E (z : D.host.E) = 1 →
      Valued.v (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (z : D.host.E)) < 1 →
      χ.locK Q (k Q) = χ.locK Q z := by
    intro Q z hz h
    refine loc_eq_of_tame χ Q (ht Q) _ _ ((GlobalTheory.CharLocProd.val_algebraMap Q _).trans hz) ?_
    have e4 : ((Formalism.L2.Host.atFin Q (k Q) : (Q.adicCompletion D.host.E)ˣ) : Q.adicCompletion D.host.E) -
        (Formalism.L2.Host.atFin Q z : (Q.adicCompletion D.host.E)ˣ) =
        (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (z : D.host.E)) -
          (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (k Q : D.host.E)) := by
      show algebraMap D.host.E _ (k Q : D.host.E) - algebraMap D.host.E _ (z : D.host.E) = _
      ring
    rw [e4]
    exact Valuation.map_sub_lt _ h (hkc Q)
  have hfin : {Q : Pl D.host.E | Q.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hx1 (P ∪ hfin.toFinset) k (fun Q _ => ⟨(hk Q).1, (hk Q).2.1⟩) (fun Q hQ => ⟨hv Q, fun h =>
    hQ (Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h)))⟩)
  obtain ⟨hei, her⟩ := resS_idemSum he
  rw [key]
  refine (Finset.prod_subset Finset.subset_union_left fun Q _ hQ => ?_).symm.trans
    (Finset.prod_congr rfl fun Q hQ => ?_)
  · rw [Units.val_eq_one]
    by_cases hcj : ∃ PP' ∈ P, IsConjPl PP' Q
    · obtain ⟨R, hR, hRQ⟩ := hcj
      have h5 := val_sub_lt_one Valued.v R ((G Q).comp (sigR (Af D.host.F) D.sp.cm.sig))
        (fun y hy => hGint Q _ (GlobalTheory.PlaceIdem.sig_mem D hy))
        (fun a ha => by
          obtain ⟨b, hb, hab⟩ := hRQ a ha
          have := hGlt Q b hb
          rw [hab] at this
          exact this) e hei 1 (by rw [her R hR, RingHom.map_one])
      have h6 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) = 1 := rfl
      rw [h6, RingHom.map_one, RingHom.comp_apply, ← GlobalTheory.PlaceIdem.finPart_cA] at h5
      have h7 : G Q (finPart D (cA D e)) ≠ 0 := by
        intro h
        rw [h, zero_sub, Valuation.map_neg, map_one] at h5
        exact lt_irrefl _ h5
      have h8 : G Q (finPart D (x : AE D)) = 1 := by
        refine mul_left_cancel₀ h7 ?_
        rw [← RingHom.map_mul, ← RingHom.map_mul, hxe, mul_one]
      rw [hloc Q 1 (by rw [Units.val_one, map_one]) (by
        rw [h8, Units.val_one, map_one, sub_self, map_zero]
        exact zero_lt_one), map_one]
    · exact hunr Q hQ hcj _ ((GlobalTheory.CharLocProd.val_algebraMap Q _).trans ((hk Q).1.symm.trans (hv Q)))
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u Q : kP Q)
    have haQ : a ∉ Q.asIdeal := by
      intro h
      have := Q.isPrime
      exact (u Q).ne_zero (ha ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)
    have ha0 : (a : D.host.E) ≠ 0 := fun h => haQ (RingOfIntegers.coe_eq_zero_iff.1 h ▸ Q.asIdeal.zero_mem)
    have h5 := val_sub_lt_one Valued.v Q (G Q) (hGint Q) (hGlt Q) x hx2 a ((hu Q hQ).symm.trans ha.symm)
    rw [hG1] at h5
    rw [hres Q hQ a (Units.mk0 _ ha0) (u Q) rfl ha.symm, hloc Q (Units.mk0 _ ha0)
      ((HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) Q (r := a)).2 haQ) h5]

end GlobalTheory.TameProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace ClassSumTranslate

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)

theorem card_stab (γ : Γ) (y : G) (k : J) :
    Nat.card (Bridge.stab ι J (ι γ * y * k)) = Nat.card (Bridge.stab ι J y) := by
  refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun δ => ?_)
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (ι γ * y * k)⁻¹ * ι δ * (ι γ * y * k) =
      (k : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * k := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInnerIndep : Bridge.AdInnerIndep ι ρ J χ := by
  intro hρ hχ I I' _ _ y y' hy hy' F hF F' hF'
  choose σ hσ using fun i => (hy' (y i)).exists
  have hinj : Function.Injective σ := by
    intro i j hij
    obtain ⟨γ, k, h1⟩ := hσ i
    obtain ⟨γ', k', h2⟩ := hσ j
    refine (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨γ * γ'⁻¹, k'⁻¹ * k, ?_⟩
    rw [h1, h2, hij]; simp [mul_assoc]
  have hsurj : Function.Surjective σ := by
    intro j
    obtain ⟨i, γ, k, h1⟩ := (hy (y' j)).exists
    obtain ⟨γ', k', h2⟩ := hσ i
    refine ⟨i, (hy' (y' j)).unique ⟨γ * γ', k' * k, ?_⟩ ⟨1, 1, by simp⟩⟩
    rw [h1, h2]; simp [mul_assoc]
  unfold Bridge.adInner
  refine Fintype.sum_bijective σ ⟨hinj, hsurj⟩ _ _ fun i => ?_
  obtain ⟨γ, k, h⟩ := hσ i
  rw [h, card_stab, hF γ _ k, hF' γ _ k, inner_smul_left, inner_smul_right, hρ, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ]
  simp

variable {J} in
theorem stab_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) (y : G) :
    Bridge.stab ι J (y * κ) = Bridge.stab ι J y := by
  ext δ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← hκ (y⁻¹ * ι δ * y)]
  simp [mul_assoc]

variable {J} in
theorem isReps_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) {I : Type} {y : I → G}
    (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * κ := by
  intro h
  refine (existsUnique_congr fun i => ?_).1 (hy (h * κ⁻¹))
  constructor
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨_, (hκ k).2 k.2⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at e
    rw [e]; simp [mul_assoc]
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨κ * k * κ⁻¹, (hκ _).1 (by simpa [mul_assoc] using k.2)⟩, ?_⟩
    rw [e]; simp [mul_assoc]

theorem translate (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (κ : l.Q) {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) :
    (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) ∈ Bridge.AdForms ι ρ l.J l.χ ∧
      Bridge.adInner ι l.J y (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ))
        (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) = Bridge.adInner ι l.J y F F := by
  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := fun k =>
    ⟨fun h => by simpa [mul_assoc] using hn _ (l.Q.inv_mem κ.2) _ h, hn _ κ.2 _⟩
  constructor
  · intro γ h k
    have e := hF γ (h * κ) ⟨_, (hκ k).2 k.2⟩
    have e2 : l.χ ⟨_, (hκ k).2 k.2⟩ = l.χ k := by
      rw [← l.ch_J, ← l.ch_J]
      have : (⟨(κ : G)⁻¹ * k * κ, l.J_le ((hκ k).2 k.2)⟩ : l.Q) = κ⁻¹ * ⟨k, l.J_le k.2⟩ * κ := rfl
      simp only
      rw [this, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    rw [e2] at e
    simp only
    rw [map_smul, smul_comm, ← e]
    simp [mul_assoc]
  · rw [adInnerIndep ι ρ l.J l.χ hρ (fun k => by rw [← l.ch_J]; exact hch _) I I y _ hy
      (isReps_mul ι hκ hy) F hF F hF]
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stab_mul ι hκ, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
      Complex.conj_mul', norm_inv, hch]
    simp

theorem translate_model (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (M : Links.HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ l.J l.χ) (Bridge.adInner ι l.J y)) (κ : l.Q) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖ := by
  have hx : M.e x ∈ Bridge.AdForms ι ρ l.J l.χ := by
    rw [← hM.2.1]; exact ⟨x, rfl⟩
  obtain ⟨h1, h2⟩ := translate ι ρ l hρ hn hch hy κ hx
  rw [← hM.2.1] at h1
  obtain ⟨x', hx'⟩ := h1
  refine ⟨x', fun h => congrFun hx' h, ?_⟩
  have h3 : inner ℂ x' x' = inner ℂ x x := by
    rw [hM.2.2, hM.2.2, hx']; exact h2
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h3]

end Generic

theorem norm_char {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) (x : M) : ‖(c x : ℂ)‖ = 1 := by
  have h : IsOfFinOrder (((Units.coeHom ℂ).comp c) x) := MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite x)
  exact h.norm_eq_one

variable {D : D7}

theorem norm_levFn (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) x) = 1 := subgroupCharExtension_one_apply _ _
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => by
    first | infer_instance | exact Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  unfold levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_char _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_char _ _

theorem lev_conj (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {q k : GL (Fin V.rank) (Lev.EAf D)} (hq : q ∈ lev D.sp.cm V.gram β (flagL L))
    (hk : k ∈ lev D.sp.cm V.gram β (flag1L L)) : q⁻¹ * k * q ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have hq' : q ∈ parLev D.sp.cm V.gram β L := hq.1
  have hk' : k ∈ parLev D.sp.cm V.gram β L := hk.1
  have hk2 : rTup β L k ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2
  have h1 : q⁻¹ * k * q ∈ parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq'
  have h2 : rTup β L (q⁻¹ * k * q) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := by
    rw [Subgroup.mem_bot] at hk2 ⊢
    rw [rTup_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq', rTup_mul (Subgroup.inv_mem _ hq') hk',
      rTup_inv hq', hk2, mul_one, inv_mul_cancel]
  exact ⟨h1, h2⟩

theorem comap_conj {G H : Type} [Group G] [Group H] (f : G →* H) {Q J : Subgroup H}
    (h : ∀ q ∈ Q, ∀ k ∈ J, q⁻¹ * k * q ∈ J) : ∀ q ∈ Q.comap f, ∀ k ∈ J.comap f, q⁻¹ * k * q ∈ J.comap f := by
  intro q hq k hk
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact h _ hq _ hk

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ q ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, q⁻¹ * k * q ∈ (levEnv V β L).J :=
  comap_conj (finHom V).range.subtype (comap_conj (Formalism.UG.bc (swapAE D)) fun _ hq _ hk => lev_conj V β L hq hk)

theorem model (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (levEnv_normal V β L) (fun q => norm_levFn V β L _) hy M hM ⟨_, hq⟩ x

end ClassSumTranslate

theorem translate_unitary_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HV → R.models_cV → ∀ i t g0 κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∀ y : (R.HV i t).H, ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) ∧ ‖y'‖ = ‖y‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hH hc i t g0 κ hκ y
  exact ClassSumTranslate.model _ _ _ _ (hc i) _ _ (R.B.L i t).pres.reps (hH i t) g0 κ hκ y

end GlobalTheory
end

