import Mathlib
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0319
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepTrivialAbove
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TrivAbove

variable {E : Type} [Field E] [NumberField E]

theorem one_coord' (w : HeightOneSpectrum (𝓞 E)) : (1 : Af E) w = 1 := rfl

theorem mul_coord' (x y : Af E) (w : HeightOneSpectrum (𝓞 E)) : (x * y) w = x w * y w := rfl

theorem inv_coord' (z : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : (↑z⁻¹ : Af E) w = ((z : Af E) w)⁻¹ := by
  show (((coord w z)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
  rw [Units.val_inv_eq_inv_val, coe_coord]

open Classical in

theorem prod_single_coord (S : Finset (HeightOneSpectrum (𝓞 E)))
    (x : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w' : HeightOneSpectrum (𝓞 E)) :
    ((∏ w ∈ S, single w (x w) : (Af E)ˣ) : Af E) w' = if w' ∈ S then (x w' : w'.adicCompletion E) else 1 := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, one_coord']; simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul, mul_coord', ih]
    by_cases h : w' = a
    · subst h; simp [ha, single_self]
    · rw [suppAt_single a (x a) w' h]; simp [h]

theorem mem_hatOUnits [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) (z : (Af E)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((z : Af E) w - 1) <
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) :
    z ∈ hatOUnits c := by
  have key : ∀ z : Af E, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w - 1) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) → z ∈ hatO c :=
    fun z h => (GlobalTheory.T.mem_completedOrder_iff_placewise E c hc z).2 ⟨1, one_mem _, fun w => by rw [one_coord', map_one], h⟩
  refine ⟨key _ fun w => (hz w).le, key _ fun w => ?_⟩
  have h1 : Valued.v ((z : Af E) w - 1) < Valued.v (1 : w.adicCompletion E) := by
    rw [map_one]
    exact (hz w).trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hv : Valued.v ((z : Af E) w) = 1 := by
    have := Valuation.map_eq_of_sub_lt _ h1
    rwa [map_one] at this
  have hz0 : (z : Af E) w ≠ 0 := by rw [← coe_coord]; exact (coord w z).ne_zero
  show Valued.v ((↑z⁻¹ : Af E) w - 1) ≤ _
  rw [inv_coord']
  have he : ((z : Af E) w)⁻¹ - 1 = -(((z : Af E) w - 1) * ((z : Af E) w)⁻¹) := by
    field_simp; ring
  rw [he, Valuation.map_neg, map_mul, map_inv₀, hv, inv_one, mul_one]
  exact (hz w).le

theorem exists_rep_trivial_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (l : ℕ),
    c ≠ ⊥ → l.Prime → ∀ q : PicO c, ∃ y : (Af E)ˣ, (QuotientGroup.mk y : PicO c) = q ∧
      ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1 := by
  intro E _ _ _ c l hc hl q
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hl0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
    exact (Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units hfin.toFinset (fun w => (coord w y0)⁻¹)
    (fun w => (multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))
  set A : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom a with hAdef
  set y1 : (Af E)ˣ := A * y0 with hy1
  set u : (Af E)ˣ := ∏ w ∈ hfin.toFinset, single w (coord w y1) with hudef
  have hA : A ∈ princ ⊔ hatOUnits c := Subgroup.mem_sup_left ⟨a, rfl⟩
  have hu : u ∈ princ ⊔ hatOUnits c := by
    refine Subgroup.mem_sup_right (mem_hatOUnits hc u fun w => ?_)
    rw [hudef, prod_single_coord]
    split_ifs with hw
    · rw [coe_coord, hy1, Units.val_mul, mul_coord']
      have hAw : (A : Af E) w = algebraMap E (w.adicCompletion E) (a : E) := rfl
      have := ha w hw
      rw [hAw]
      simpa [Units.val_inv_eq_inv_val, coe_coord] using this
    · rw [sub_self, map_zero]; exact WithZero.exp_pos.bot_lt
  refine ⟨y1 * u⁻¹, ?_, fun w hw => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff A).2 hA, (QuotientGroup.eq_one_iff u).2 hu, one_mul, inv_one, mul_one]
  · have hwT : w ∈ hfin.toFinset := hfin.mem_toFinset.2 hw
    rw [Units.val_mul, mul_coord', inv_coord', hudef, prod_single_coord, if_pos hwT, coe_coord]
    exact mul_inv_cancel₀ (by rw [← coe_coord]; exact (coord w y1).ne_zero)

end GlobalTheory.CMVal.TrivAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links
  GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameFinitePart

theorem exists_chrEq_val (D : D7) (χ : HChar D.host.E) (hχ : χ.IsUnitary) :
    ∃ c, ChrEq c χ ∧ ∀ x, ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c', ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩, fun x => ⟨u x, rfl⟩⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
  · refine (hcoe _).trans ?_
    have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
      (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
    exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
  · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
    change Θ (x : Formalism.L2.Theta.AE D) = _
    rw [hx, hloc P e he]

theorem exists_lift (D : D7) (y : (AfE D)ˣ) : ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) = y ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
  obtain ⟨a, a1, a2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 (y : AfE D)
  obtain ⟨b, b1, b2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 ((y⁻¹ : (AfE D)ˣ) : AfE D)
  have h : a * b = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, a1, b1, RingHom.map_one, mul_one])
    (by rw [RingHom.map_mul, a2, b2, RingHom.map_one, Units.mul_inv])
  exact ⟨⟨a, b, h, (mul_comm b a).trans h⟩, a1, a2, b2⟩

theorem exists_unit_ne_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (ht : χ.TameAt P) (hr : ¬ χ.UnrAt P) : ∃ k : Lˣ, P.valuation L (k : L) = 1 ∧ χ.locK P k ≠ 1 := by
  by_contra hn
  refine hr fun x hx => ?_
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-1 : ℤ)).preimage (continuous_sub_left (x : P.adicCompletion L))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L) P).exists_mem_open h1 ⟨x, by simp⟩
  have hk' : Valued.v ((x : P.adicCompletion L) - algebraMap L _ k) ≤ WithZero.exp (-1 : ℤ) := hk
  have hx' : Valued.v (x : P.adicCompletion L) = 1 := hx
  have hv : Valued.v (algebraMap L (P.adicCompletion L) k) = 1 := by
    rw [← hx']
    refine (Valuation.map_eq_of_sub_lt _ ?_)
    rw [Valuation.map_sub_swap, hx']
    refine hk'.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hv' : P.valuation L k = 1 := (GlobalTheory.BaseIdeleTriv.val_algebraMap P k).symm.trans hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv'
  have h2 : χ.loc P (atFin P (Units.mk0 k hk0)) = 1 := by
    by_contra h
    exact hn ⟨Units.mk0 k hk0, hv', h⟩
  have e : ((x * (atFin P (Units.mk0 k hk0))⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
      x * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have h0 : algebraMap L (P.adicCompletion L) k ≠ 0 := by simpa using hk0
  have h3 := ht (x * (atFin P (Units.mk0 k hk0))⁻¹) (by
    unfold IsUnitAt
    rw [e, map_mul, map_inv₀, hx', hv]; simp) (by
    have : (x : P.adicCompletion L) * (algebraMap L (P.adicCompletion L) k)⁻¹ - 1 =
        ((x : P.adicCompletion L) - algebraMap L _ k) * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
      field_simp
    rw [e, this, map_mul, map_inv₀, hv, inv_one, mul_one]
    simpa using hk')
  rwa [map_mul, map_inv, h2, inv_one, mul_one] at h3

theorem loc_sub_one {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) (N : ℕ)
    (hN : (N : E) ≠ 0) : f (1 + e * (i k - 1)) - 1 = N • f (e * i ((k - 1) / N)) := by
  rw [← map_nsmul, ← mul_smul_comm, ← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hN, map_add, map_one, map_sub, map_one,
    add_sub_cancel_left]

theorem loc_eq {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) :
    f (1 + e * (i k - 1)) = 1 + f (e * i (k - 1)) := by
  rw [map_add, map_one, map_sub, map_one]

theorem loc_mul_inv {E A : Type} [Field E] [CommRing A] (i : E →+* A) (e : A) (he : e * e = e) (k : Eˣ) :
    (1 + e * (i k - 1)) * (1 + e * (i ((k⁻¹ : Eˣ) : E) - 1)) = 1 := by
  have hkk : i (k : E) * i ((k⁻¹ : Eˣ) : E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination (i (k : E) - 1) * (i ((k⁻¹ : Eˣ) : E) - 1) * he + e * hkk

set_option maxHeartbeats 800000 in

theorem exists_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (k : D.host.Eˣ)
    (hk : P.valuation D.host.E (k : D.host.E) = 1) (N : ℕ) (hN : (N : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ (e : AE D) (x : (AE D)ˣ), IsPlIdem D e P ∧ (x : AE D) = locE D e (k : D.host.E) ∧
      IntUnit (Units.map (finPart D).toMonoidHom x) ∧ CongOne N (Units.map (finPart D).toMonoidHom x) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -, e1, e2⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hee : e * e = e := he.1
  have hint : ∀ t : D.host.E, P.valuation D.host.E t ≤ 1 → finPart D (e * incA D t) ∈ intAE D := fun t ht => by
    have h4 : finPart D (incA D t) = (1 : Af D.host.F) ⊗ₜ[D.host.F] t := rfl
    rw [h2, RingHom.map_mul, map_mul, h4, h1]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_mul_apply]
    by_cases hQ : Q = P
    · subst hQ
      rw [e1, one_mul, GlobalTheory.BaseIdeleTriv.adele_algebraMap_apply, GlobalTheory.BaseIdeleTriv.val_algebraMap]
      exact ht
    · rw [e2 Q hQ, zero_mul, map_zero]
      exact zero_le
  have hone : (1 : AfE D) ∈ intAE D := by
    rw [h2, map_one]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_one_apply, map_one]
  have hloc : ∀ t : D.host.E, P.valuation D.host.E t = 1 → finPart D (locE D e t) ∈ intAE D := fun t ht => by
    rw [show finPart D (locE D e t) = _ from loc_eq (incA D) (finPart D) e t]
    exact add_mem hone (hint _ (Valuation.map_sub_le _ ht.le (map_one _).le))
  have hm : locE D e (k : D.host.E) * locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) = 1 := loc_mul_inv (incA D) e hee k
  have hN1 : P.valuation D.host.E (N : D.host.E) = 1 := by
    have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := (N : 𝓞 D.host.E))).2 hN
    simpa using this
  have hN0 : (N : D.host.E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hN1
    exact zero_ne_one hN1
  refine ⟨e, ⟨_, _, hm, (mul_comm _ _).trans hm⟩, he, rfl, ⟨hloc _ hk, hloc _ ?_⟩,
    finPart D (e * incA D (((k : D.host.E) - 1) / N)), hint _ ?_, ?_⟩
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hk, inv_one]
  · rw [map_div₀, hN1, div_one]
    exact Valuation.map_sub_le _ hk.le (map_one _).le
  · exact loc_sub_one (incA D) (finPart D) e k N hN0

set_option maxHeartbeats 1000000 in

theorem exists_xiRec : ∀ (D : D7) (p : ℕ) (δ : Formalism.L2.Host.HChar D.host.E), (p = D.host.pde ∨ p = D.host.pde') → Formalism.L2.Host.IsDelta (H := D.host) p δ → (∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D) → ∃ (χ : (AE D)ˣ →* Circle) (de : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ), ChrEq χ δ ∧ XiRec D p de ∧ ∀ (x : (AE D)ˣ) (y : (GlobalTheory.FinalJoin.AfE D)ˣ), Formalism.L2.Theta.finPart D (x : AE D) = (y : GlobalTheory.FinalJoin.AfE D) → ((de y : ℂˣ) : ℂ) = ((χ x : Circle) : ℂ) := by
  intro D p χ hp hδ hval
  obtain ⟨n, hn, ho⟩ := hδ.fin
  obtain ⟨c, h, hcv⟩ := exists_chrEq_val D χ fun x => by
    have h1 : χ.1 x ^ n = 1 := by
      have := DFunLike.congr_fun (congrArg Subtype.val ho) x
      simpa [MonoidHom.pow_apply] using this
    have h2 : ((χ.1 x : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'
  have h1 : ∀ x, c x ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  have h2 : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1 := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
    rw [map_pow, h1]
  have h3 : ∀ a, c (idF D a) = 1 := fun a => by
    let b : (AF D.host.F)ˣ := Units.map ((MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))) a
    let b' : (AF D.host.F)ˣ := Units.map ((MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))) a
    have e : a = b' * b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e, map_mul, map_mul, h2 (idF D b') rfl, GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ h hδ.triv b rfl, one_mul]
  obtain ⟨d, hd⟩ := GlobalTheory.DetRootChar.circle_hom_factor (Units.map (finPart D).toMonoidHom) c
    fun x hx => h2 x (congrArg Units.val hx)
  have hd' : ∀ (x : (AE D)ˣ) (y : (AfE D)ˣ), finPart D (x : AE D) = (y : AfE D) → d y = c x := fun x y hxy => by
    rw [← hd x]
    exact congrArg d (Units.ext hxy.symm)
  have hone : ∀ y, d y = 1 → (Circle.toUnits.comp d) y = 1 := fun y hy => by
    rw [MonoidHom.comp_apply, hy, map_one]
  have hcoe : ∀ y, (((Circle.toUnits.comp d) y : ℂˣ) : ℂ) = ((d y : Circle) : ℂ) := fun y => by simp
  have hpp : p.Prime ∧ ∀ i, p ≠ D.host.g i := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, fun i => (D.host.pde_ne_g i).2⟩
  refine ⟨c, Circle.toUnits.comp d, h, ⟨fun y a hy => hone y ?_, fun y a hy => hone y ?_, fun y hy hc => hone y ?_, ?_,
    ⟨n, hn, fun y => ?_⟩, fun y => ?_⟩, fun x y hxy => by rw [hcoe, hd' x y hxy]⟩
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨b, z, hz, hxz⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x (by
      rw [hx, hy]
      change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
      rw [map_one])
    rw [hd' x y hx, hxz, map_mul, h3, h2 z hz, mul_one]
  · have ha : a ≠ 0 := by
      rintro rfl
      obtain ⟨ι, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
      obtain ⟨P, -⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
      have e := congrArg (fun z => ι z P) y.mul_inv
      rw [hy, TensorProduct.tmul_zero, zero_mul, map_zero, map_one] at e
      exact zero_ne_one (α := P.adicCompletion D.host.E) e
    rw [hd' (Units.map (incA D).toMonoidHom (Units.mk0 a ha)) y hy.symm, h.1.2]
  · obtain ⟨x, hx0, hx, hx'⟩ := exists_lift D y
    rw [hd' x y hx]
    exact GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ h hδ.tame p hδ.unr x ⟨hx0, hx ▸ hy.1, hx' ▸ hy.2⟩ (hx ▸ hc)
  · obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
    obtain ⟨k, hk, hk1⟩ := exists_unit_ne_one χ P (hδ.tame P) fun hu => by
      have := (hδ.ine P hP 1).1 fun x hx => by rw [hu x hx, one_pow]
      omega
    have hcop : Nat.Coprime p (D.host.g 0 * D.host.g 1) :=
      ((Nat.coprime_primes hpp.1 (D.host.g_prime 0)).2 (hpp.2 0)).mul_right
        ((Nat.coprime_primes hpp.1 (D.host.g_prime 1)).2 (hpp.2 1))
    obtain ⟨e, x, he, hx, i1, i2⟩ := exists_local D P k hk (D.host.g 0 * D.host.g 1) fun hm => by
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.E) hcop)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hm)))
    refine ⟨_, i1, i2, fun hh => hk1 (Units.ext ?_)⟩
    rw [← h.2 P e he k x hx, ← hd x, ← hcoe, hh]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    rw [MonoidHom.comp_apply, ← map_pow, hd' x y hx, h1, map_one]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨z, hz⟩ := hcv x
    rw [hcoe, hd' x y hx, hz]
    exact hval z

end GlobalTheory.TameFinitePart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalOfZariskiSheafOpenCharts
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_universal_of_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) := by
  intro F hsep hglue Ix U x inj hW cov
  have hF : Presieve.IsSheaf Scheme.zariskiTopology F := GlobalTheory.T.isSheaf_of_open_immersion_local_glue F hsep hglue
  let W : ∀ (_ : Ix) (Z : Scheme.{0}), F.obj (op Z) → Z.Opens :=
    fun i Z y => Classical.choose (hW i Z y)
  have hWs : ∀ i (Z : Scheme.{0}) (y : F.obj (op Z)) (Y : Scheme.{0}) (a : Y ⟶ Z),
      (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W i Z y :=
    fun i Z y => Classical.choose_spec (hW i Z y)
  have hrep : F.IsRepresentable := by
    refine GeneratorFunctor.isRepresentable_of_charts F hF U x W ?_ ?_ ?_
    · intro j Z y Z' a
      rw [Set.range_subset_iff]
      refine ((hWs j Z y Z' a).symm.trans ?_)
      exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩
    · intro j Z g g' h
      exact inj j Z g g' h
    · intro Z y z
      obtain ⟨i, Y, a, u, ⟨q, rfl⟩, h⟩ := cov Z y z
      exact ⟨i, (hWs i Z y Y a).1 ⟨u, h⟩ q⟩
  refine ⟨F.reprX, F.reprx, fun T y => ?_⟩
  refine ⟨F.representableBy.homEquiv.symm y, ?_, ?_⟩
  · have := F.representableBy.homEquiv_eq (F.representableBy.homEquiv.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · intro g hg
    apply F.representableBy.homEquiv.injective
    rw [Equiv.apply_symm_apply, F.representableBy.homEquiv_eq, ← hg]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationPowPrimePowSubGe
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PowLim

theorem pow_prime_step {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ}
    (hp : p.Prime) (hvp : v (p : C) = 1) {a b : C} (ha : 0 ≤ v a) (hb : 0 ≤ v b) {t ε : ℝ}
    (hεt : ε ≤ t) (hε1 : ε ≤ 1) (ht : (t : WithTop ℝ) ≤ v (a - b)) :
    ((t + ε : ℝ) : WithTop ℝ) ≤ v (a ^ p - b ^ p) := by
  let R : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : 0 ≤ v a := ha
        have hb' : 0 ≤ v b := hb
        show 0 ≤ v (a * b)
        rw [v.map_mul]
        exact add_nonneg ha' hb'
      one_mem' := by
        show 0 ≤ v 1
        rw [v.map_one]
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (v.map_add _ _)
      zero_mem' := by
        show 0 ≤ v 0
        rw [v.map_zero]; exact le_top
      neg_mem' := fun {a} ha => by
        show 0 ≤ v (-a)
        rw [v.map_neg]; exact ha }
  have haR : a ∈ R := ha
  have hbR : b ∈ R := hb
  have hdR : a - b ∈ R := R.sub_mem haR hbR
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨a - b, hdR⟩ : R) ⟨b, hbR⟩
  have hr' := congrArg (fun z : R => (z : C)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast,
    sub_add_cancel] at hr'
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have e : a ^ p - b ^ p = (a - b) * (a - b) * (a - b) ^ k + (p : C) * (a - b) * (b * r) := by
    rw [hr']
    have : (a - b) ^ p = (a - b) * (a - b) * (a - b) ^ k := by rw [hk]; ring
    rw [this]; ring
  have h1 : (0 : WithTop ℝ) ≤ v ((a - b) ^ k) := R.pow_mem hdR k
  have h2 : (0 : WithTop ℝ) ≤ v (b * (r : C)) := R.mul_mem hbR r.2
  have hε : (ε : WithTop ℝ) ≤ v (a - b) := le_trans (WithTop.coe_le_coe.2 hεt) ht
  have hε1' : (ε : WithTop ℝ) ≤ 1 := by exact_mod_cast hε1
  rw [e]
  refine le_trans (le_min ?_ ?_) (v.map_add _ _)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add]
    exact le_trans (add_le_add ht hε) (le_add_of_nonneg_right h1)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add, hvp, add_comm (t : WithTop ℝ)]
    exact le_trans (add_le_add hε1' ht) (le_add_of_nonneg_right h2)

theorem pow_prime_pow_close : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ x y : C, IsIntV v x → IsIntV v y → 0 < v (x - y) → ∀ r : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
  intro C _ v p hp hvp x y hx hy hxy r
  have hx' : 0 ≤ v x := hx
  have hy' : 0 ≤ v y := hy
  obtain ⟨ε, hε0, hε1, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (ε : WithTop ℝ) ≤ v (x - y) := by
    generalize v (x - y) = w at hxy
    induction w using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_rfl, le_top⟩
    | coe s =>
      have hs : 0 < s := by exact_mod_cast hxy
      exact ⟨min s 1, lt_min hs one_pos, min_le_right _ _, WithTop.coe_le_coe.2 (min_le_left _ _)⟩
  have hpow : ∀ (z : C) (n : ℕ), 0 ≤ v z → 0 ≤ v (z ^ n) := by
    intro z n hz
    rw [v.map_pow]
    exact nsmul_nonneg hz n
  have key : ∀ N : ℕ, ((((N : ℝ) + 1) * ε : ℝ) : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
    intro N
    induction N with
    | zero => simpa using hε
    | succ N ih =>
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have := pow_prime_step v hp hvp (hpow x (p ^ N) hx') (hpow y (p ^ N) hy')
        (t := ((N : ℝ) + 1) * ε) (ε := ε) (by nlinarith) hε1 ih
      rw [← pow_mul, ← pow_mul, ← pow_succ] at this
      refine le_trans (WithTop.coe_le_coe.2 (le_of_eq ?_)) this
      push_cast; ring
  obtain ⟨M, hM⟩ := exists_nat_gt (r / ε)
  refine ⟨M, fun N hN => le_trans (WithTop.coe_le_coe.2 ?_) (key N)⟩
  have h1 : (M : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_lt_iff₀ hε0] at hM
  nlinarith

end GlobalTheory.PowLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_twist_heckeCharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (νS νT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 → ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h) := by
  first | exact @GlobalTheory.WeilChange.exists_weilDatum_twist | exact GlobalTheory.WeilChange.exists_weilDatum_twist | (intros; apply GlobalTheory.WeilChange.exists_weilDatum_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPolynomialDegreeLeRankStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_polynomial_degree_le_rank : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → R.Char F → ∀ (p : A.fam.base.Ix), ∀ P ∈ A.ok A.μ0, (RealDat.polE (A := A) p.1 P).natDegree ≤ D.R.r := by
  first | exact @GlobalTheory.ResDeg.natDegree_polE_le | exact GlobalTheory.ResDeg.natDegree_polE_le | (intros; apply GlobalTheory.ResDeg.natDegree_polE_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalMatrixCoefficientSpan
section
namespace GlobalTheory.Proof.CoeffSpan

theorem finiteDimensional_coeffSpan (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine ⟨{ toFun := fun A => ℓ (A w), map_add' := fun A B => by simp, map_smul' := fun c A => by simp }, ?_⟩
    rfl
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.Proof.CoeffSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_killed_eq_of_equal_multiplicities : ∀ (H : Type) [Group H] [TopologicalSpace H] (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), IsDecomp ρ C → IsDecomp ρ' C' → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → GlobalTheory.PRep.IsAdmissible σ → killed σ I ≠ ⊥ → Module.rank ℂ (homInto σ ρ C) = Module.rank ℂ (homInto σ ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ (C ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ (C ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) := by
  first | exact @GlobalTheory.RepCount.finrank_inf_killed_eq | exact GlobalTheory.RepCount.finrank_inf_killed_eq | (intros; apply GlobalTheory.RepCount.finrank_inf_killed_eq <;> assumption)
end

