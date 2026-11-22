import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.TorsionCard

variable {l : ℕ} [hl : Fact l.Prime]

noncomputable def red (l : ℕ) [Fact l.Prime] : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom

theorem red_val (x : ℤ_[l]ˣ) : (red l x : ZMod l) = PadicInt.toZMod (x : ℤ_[l]) := rfl

theorem eq_one_of_red (h2 : l ≠ 2) (x : ℤ_[l]ˣ) (hx : IsOfFinOrder x) (h1 : red l x = 1) :
    x = 1 := by
  have hpos : 0 < orderOf x := hx.orderOf_pos
  have hpow : ((x : ℤ_[l])) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hred : PadicInt.toZMod (x : ℤ_[l]) = 1 := by
    rw [← red_val, h1, Units.val_one]
  exact Units.ext (GlobalTheory.padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hpos.ne' hpow hred)

theorem exists_lift (h2 : l ≠ 2) (u : (ZMod l)ˣ) :
    ∃ x : ℤ_[l]ˣ, IsOfFinOrder x ∧ red l x = u := by
  classical
  have hl3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
  set a : ℤ_[l] := ((u : ZMod l).val : ℤ_[l]) with ha
  have hred_a : PadicInt.toZMod a = (u : ZMod l) := by
    rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have norm_of : ∀ y : ℤ_[l], PadicInt.toZMod y ≠ 0 → ‖y‖ = 1 := by
    intro y hy
    by_contra hne
    have hlt : ‖y‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one y) hne
    apply hy
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton, ← PadicInt.norm_lt_one_iff_dvd]
    exact hlt
  have lt_of : ∀ y : ℤ_[l], PadicInt.toZMod y = 0 → ‖y‖ < 1 := by
    intro y hy
    rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hy
  let F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1
  have hF : PadicInt.toZMod (F.aeval a) = 0 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one, hred_a]
    rw [sub_eq_zero, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one]
  have hF' : PadicInt.toZMod (F.derivative.aeval a) ≠ 0 := by
    simp [F, hred_a, Polynomial.derivative_X_pow]
    rw [ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [norm_of _ hF', one_pow]; exact lt_of _ hF
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma hnorm
  have hz1 : z ^ (l - 1) = 1 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one] at hz
    exact sub_eq_zero.mp hz
  have e : l - 1 = (l - 2) + 1 := by omega
  let x : ℤ_[l]ˣ := ⟨z, z ^ (l - 2), by rw [← pow_succ', ← e, hz1], by rw [← pow_succ, ← e, hz1]⟩
  refine ⟨x, ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l - 1, by omega, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val]
    exact hz1
  · apply Units.ext
    rw [red_val, ← hred_a, ← sub_eq_zero, ← map_sub]
    by_contra hne
    have h1 := norm_of _ hne
    rw [norm_of _ hF'] at hza
    change ‖z - a‖ < 1 at hza
    linarith

theorem card_torsion (h2 : l ≠ 2) {Γ : Type} [Group Γ] (χ : Γ →* ℤ_[l]ˣ)
    (hχ : Function.Injective χ) (hk : ∀ x, red l x = 1 → x ∈ χ.range) :
    Nat.card {g : Γ // IsOfFinOrder g} = Nat.card ((red l).comp χ).range := by
  classical
  have hcomm : ∀ a b : Γ, a * b = b * a := fun a b => hχ (by rw [map_mul, map_mul, mul_comm])
  have hfin : ∀ g : Γ, IsOfFinOrder (χ g) ↔ IsOfFinOrder g := fun g => by
    rw [← orderOf_pos_iff, ← orderOf_pos_iff, orderOf_injective χ hχ g]
  let f : {g : Γ // IsOfFinOrder g} → ((red l).comp χ).range := fun g => ⟨red l (χ g.1), g.1, rfl⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : red l (χ a) = red l (χ b) := congrArg Subtype.val hab
    have hc : Commute a b⁻¹ := hcomm a b⁻¹
    have ht : IsOfFinOrder (χ (a * b⁻¹)) := (hfin _).mpr (hc.isOfFinOrder_mul ha hb.inv)
    have h1 : red l (χ (a * b⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv, hab', mul_inv_cancel]
    have h3 := eq_one_of_red h2 _ ht h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact Subtype.ext (hχ h3)
  · rintro ⟨u, g, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_lift h2 (red l (χ g))
    have hr : red l (x⁻¹ * χ g) = 1 := by rw [map_mul, map_inv, hxu, inv_mul_cancel]
    obtain ⟨k, hk'⟩ := hk _ hr
    have hgk : χ (g * k⁻¹) = x := by
      rw [map_mul, map_inv, hk', mul_inv_rev, inv_inv, mul_inv_cancel_left]
    refine ⟨⟨g * k⁻¹, (hfin _).mp (hgk ▸ hx)⟩, Subtype.ext ?_⟩
    change red l (χ (g * k⁻¹)) = red l (χ g)
    rw [hgk, hxu]

theorem exists_chi (P : LocPrime l) :
    ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) := by
  have hn := GlobalTheory.Cyc.IsCyc.norm_eq_one P.χQ_cyc
  refine ⟨{ toFun := fun g => PadicInt.mkUnits (hn g), map_one' := ?_, map_mul' := ?_ },
    fun g => PadicInt.mkUnits_eq (hn g)⟩
  · apply Units.ext; apply PadicInt.ext
    simp
  · intro a b; apply Units.ext; apply PadicInt.ext
    simp only [Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq, map_mul]

theorem finrank_eq_relIndex (K : FinExt l) :
    Module.finrank ↥(K0 K) ↥K.1 = (GK K).relIndex (K0 K).fixingSubgroup := by
  have hle : K0 K ≤ K.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  have : FiniteDimensional ℚ_[l] (K0 K) := FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  have h1 := IntermediateField.finrank_eq_fixingSubgroup_index (E' := Om l) K.1
  have h2 := IntermediateField.finrank_eq_fixingSubgroup_index (E' := Om l) (K0 K)
  have h3 := Subgroup.relIndex_mul_index (IntermediateField.fixingSubgroup_le hle)
  have h4 := Module.finrank_mul_finrank ℚ_[l] (K0 K) K.1
  have hpos : 0 < Module.finrank ℚ_[l] (K0 K) := Module.finrank_pos
  unfold GK
  rw [← h1, ← h2] at h3
  rw [← h4, mul_comm] at h3
  exact (Nat.eq_of_mul_eq_mul_left hpos h3).symm

set_option maxHeartbeats 800000 in

theorem card_torsion_mul_finrank : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), l ≠ 2 → K.1 ≤ Ks K 1 → W.DelF.card * Module.finrank ↥(K0 K) ↥K.1 = l - 1 := by
  intro l _ P K LL n W h2 hK
  classical
  obtain ⟨χ, hχ⟩ := exists_chi P
  have hle : K0 K ≤ K.1 := inf_le_left
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  have hval : ∀ g : ↥(GK K), ((χK g : ℤ_[l]) : ℚ_[l]) = ((P.PD K).χ g : ℚ_[l]) := by
    intro g
    rw [P.PD_χ K g]
    exact hχ g
  have hO : Function.Injective (algebraMap (OL LL) LL.1) := Subtype.val_injective
  have hkey : ∀ g : ↥(GK K), W.resΓ g = 1 ↔ χK g = 1 := by
    intro g
    have hr := W.χΓ_res g
    constructor
    · intro h
      rw [h, map_one, Units.val_one, map_one] at hr
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 :=
        (algebraMap ℚ_[l] LL.1).injective (by rw [← hr, map_one])
      apply Units.ext
      apply PadicInt.ext
      rw [hval, h1]
      simp
    · intro h
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
        rw [← hval, h]
        simp
      rw [h1, map_one] at hr
      have h3 : ((W.χΓ (W.resΓ g) : (OL LL)ˣ) : OL LL) = 1 := hO (by rw [hr, map_one])
      apply W.χΓ_inj
      rw [map_one]
      exact Units.ext h3
  let ψ : W.Gam →* ℤ_[l]ˣ :=
    W.resΓ.liftOfRightInverse (Function.surjInv W.resΓ_onto)
      (Function.rightInverse_surjInv W.resΓ_onto)
      ⟨χK, fun g hg => MonoidHom.mem_ker.mpr ((hkey g).mp (MonoidHom.mem_ker.mp hg))⟩
  have hψ : ∀ g : ↥(GK K), ψ (W.resΓ g) = χK g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun γ hγ => ?_
    obtain ⟨g, rfl⟩ := W.resΓ_onto γ
    rw [hψ] at hγ
    exact (hkey g).mpr hγ
  have hfix : ∀ g : GQ l, g ∈ (K0 K).fixingSubgroup → red l (χ g) = 1 → g ∈ GK K := by
    intro g hg hr
    have hz : PadicInt.toZMod ((χ g : ℤ_[l]) - 1) = 0 := by
      rw [map_sub, ← red_val, hr, Units.val_one, map_one, sub_self]
    have hd : (l : ℤ_[l]) ^ 1 ∣ (χ g : ℤ_[l]) - 1 := by
      rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hz
    have hnorm : ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [← hχ g]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (Ideal.mem_span_singleton.mpr hd)
      simpa [PadicInt.norm_def] using this
    have hζ := (GlobalTheory.Cyc.IsCyc.fix_iff P.χQ_cyc g 1).mpr hnorm
    have hadj : g ∈ (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ 1 = 1}).fixingSubgroup :=
      (GlobalTheory.Cyc.mem_fixingSubgroup_adjoin_iff _ g).mpr fun x hx => hζ x hx
    have hKs : g ∈ (Ks K 1).fixingSubgroup := by
      unfold Ks
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hg, hadj⟩
    exact IntermediateField.fixingSubgroup_le hK hKs
  have hfd0 : FiniteDimensional ℚ_[l] (K0 K) := by
    have : FiniteDimensional ℚ_[l] K.1 := K.2
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  let K0' : FinExt l := ⟨K0 K, hfd0⟩
  have honto : ∀ c : ℤ_[l]ˣ, ∃ g ∈ (K0 K).fixingSubgroup, χ g = c := by
    intro c
    obtain ⟨g, hg, hgc⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K0' inf_le_right c
    exact ⟨g, hg, Units.ext (PadicInt.ext (by rw [hχ g, hgc]))⟩
  have hk : ∀ x : ℤ_[l]ˣ, red l x = 1 → x ∈ ψ.range := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := honto x
    exact ⟨W.resΓ ⟨g, hfix g hg hx⟩, by rw [hψ]; rfl⟩
  have hct := card_torsion h2 ψ hψinj hk
  have hdel : W.DelF.card = Nat.card {γ : W.Gam // IsOfFinOrder γ} := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun γ => by
      rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one])
  let G0 := (K0 K).fixingSubgroup
  let F : ↥G0 →* (ZMod l)ˣ := (red l).comp (χ.comp G0.subtype)
  have hF : Function.Surjective F := by
    intro u
    obtain ⟨x, -, hxu⟩ := exists_lift h2 u
    obtain ⟨g, hg, hgx⟩ := honto x
    exact ⟨⟨g, hg⟩, by simp [F, hgx, hxu]⟩
  let H0 := (GK K).subgroupOf G0
  have hkerF : F.ker ≤ H0 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    exact Subgroup.mem_subgroupOf.mpr (hfix g g.2 hg)
  have hidx : H0.index = (H0.map F).index := by
    rw [← Subgroup.index_comap_of_surjective _ hF, Subgroup.comap_map_eq_self hkerF]
  have hmap : H0.map F = ((red l).comp ψ).range := by
    ext u
    constructor
    · rintro ⟨g0, hg0, rfl⟩
      refine ⟨W.resΓ ⟨g0, Subgroup.mem_subgroupOf.mp hg0⟩, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
    · rintro ⟨γ, rfl⟩
      obtain ⟨g, rfl⟩ := W.resΓ_onto γ
      refine ⟨⟨g, IntermediateField.fixingSubgroup_le hle g.2⟩, Subgroup.mem_subgroupOf.mpr g.2, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
  have hcard := Subgroup.card_mul_index (H0.map F)
  rw [Nat.card_eq_fintype_card (α := (ZMod l)ˣ), ZMod.card_units] at hcard
  rw [finrank_eq_relIndex, hdel, hct, ← hmap]
  change _ * H0.index = _
  rw [hidx]
  exact hcard

end GlobalTheory.TorsionCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyHamilton
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

open Polynomial

private theorem pseudo_character_sum_cons_expand {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ) (a : M)
    (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a r) =
      T a * _root_.GlobalTheory.PsChar.alt T n r -
        ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i)) := rfl

private theorem pseudo_character_sum_cons_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (ih : ∀ (w : Fin n → M) (τ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (w ∘ τ) = _root_.GlobalTheory.PsChar.alt T n w)
    (a : M) (w : Fin n → M) (τ : Equiv.Perm (Fin n)) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a (w ∘ τ)) =
      _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a w) := by
  rw [pseudo_character_sum_cons_expand, pseudo_character_sum_cons_expand, ih]
  congr 1
  have : ∀ i, Function.update (w ∘ τ) i (a * (w ∘ τ) i) =
      Function.update w (τ i) (a * w (τ i)) ∘ τ := fun i => by
    rw [Function.update_comp_equiv, Equiv.symm_apply_apply]; rfl
  simp only [this, ih]
  exact Equiv.sum_comp τ (fun j => _root_.GlobalTheory.PsChar.alt T n (Function.update w j (a * w j)))

private theorem alt_cons_cons_lemma_5 {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      T a * T b * _root_.GlobalTheory.PsChar.alt T n r
      - T a * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * r i))
      - T b * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i))
      - T (a * b) * _root_.GlobalTheory.PsChar.alt T n r
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * b * r i))
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i))
      + ∑ i, ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
  rw [pseudo_character_sum_cons_expand, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, Fin.cons_update, pseudo_character_sum_cons_expand]
  have hin : ∀ i : Fin n, ∑ l, _root_.GlobalTheory.PsChar.alt T n
      (Function.update (Function.update r i (a * r i)) l
        (b * Function.update r i (a * r i) l)) =
      _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) +
      ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
    intro i
    have hX : (∑ l : Fin n, if l = i then
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) else 0) =
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) := by simp
    rw [← hX, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [mul_assoc]
    · rw [if_neg hl, if_neg hl, zero_add, Function.update_of_ne hl]
  simp only [← Fin.cons_update, pseudo_character_sum_cons_expand, Finset.sum_sub_distrib, Function.update_self]
  simp only [hin, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem pseudo_character_sum_swap_head_pair {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) (n : ℕ) (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons b (Fin.cons a r)) := by
  rw [alt_cons_cons_lemma_5, alt_cons_cons_lemma_5, hc a b]
  have hoff : (∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l))) =
      ∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (b * r i)) l (a * r l)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · simp [hl]
    · rw [if_neg (Ne.symm hl), if_neg hl, Function.update_comm (Ne.symm hl)]
  rw [hoff]
  ring

private theorem pseudo_character_sum_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) :
    ∀ (n : ℕ) (v : Fin n → M) (σ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T n v := by
  intro n
  induction n with
  | zero => intro v σ; rfl
  | succ n ih =>
    have htail : ∀ (v : Fin (n + 1) → M) (i j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap i.succ j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v i j
      have hv : v ∘ Equiv.swap i.succ j.succ = Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap i j) := by
        funext k
        induction k using Fin.cases with
        | zero =>
          simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
            (Fin.succ_ne_zero j).symm]
        | succ k =>
          simp only [Function.comp_apply, Fin.cons_succ, Fin.tail]
          rw [(Fin.succ_injective n).swap_apply]
      rw [hv, pseudo_character_sum_cons_comp_perm T n ih, Fin.cons_self_tail]
    have h0 : ∀ (v : Fin (n + 1) → M) (j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap 0 j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v j
      cases n with
      | zero => exact j.elim0
      | succ m =>
        have h01 : ∀ v : Fin (m + 2) → M,
            _root_.GlobalTheory.PsChar.alt T (m + 2) (v ∘ Equiv.swap 0 (Fin.succ 0)) =
              _root_.GlobalTheory.PsChar.alt T (m + 2) v := by
          intro v
          obtain ⟨a, b, r, rfl⟩ : ∃ a b r, v = Fin.cons a (Fin.cons b r) :=
            ⟨_, _, _, (Fin.cons_self_tail v).symm.trans (congrArg _ (Fin.cons_self_tail _).symm)⟩
          have hv : (Fin.cons a (Fin.cons b r) : Fin (m + 2) → M) ∘ Equiv.swap 0 (Fin.succ 0) =
              Fin.cons b (Fin.cons a r) := by
            funext k
            refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
            · simp
            · simp
            · simp only [Function.comp_apply]
              rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
                (fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h))]
              simp
          rw [hv, pseudo_character_sum_swap_head_pair T hc]
        induction j using Fin.cases with
        | zero => exact h01 v
        | succ k =>
          have hp : Equiv.swap (0 : Fin (m + 2)) k.succ.succ =
              Equiv.swap (Fin.succ 0) k.succ.succ * Equiv.swap 0 (Fin.succ 0) *
                Equiv.swap (Fin.succ 0) k.succ.succ := by
            have h1 : Equiv.swap (Fin.succ 0) k.succ.succ (0 : Fin (m + 2)) = 0 :=
              Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero _).symm
            have h2 : Equiv.swap (Fin.succ 0) k.succ.succ (Fin.succ 0 : Fin (m + 2)) = k.succ.succ :=
              Equiv.swap_apply_left _ _
            have := Equiv.swap_apply_apply (Equiv.swap (Fin.succ 0) k.succ.succ) 0 (Fin.succ 0)
            rw [h1, h2, Equiv.swap_inv] at this
            exact this
          rw [hp, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Function.comp_assoc,
            ← Function.comp_assoc, htail, h01, htail]
    have hswap : ∀ (v : Fin (n + 1) → M) (x y : Fin (n + 1)),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap x y) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v x y
      induction x using Fin.cases with
      | zero =>
        induction y using Fin.cases with
        | zero => simp
        | succ j => exact h0 v j
      | succ i =>
        induction y using Fin.cases with
        | zero => rw [Equiv.swap_comm]; exact h0 v i
        | succ j => exact htail v i j
    intro v σ
    revert v
    refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ v : Fin (n + 1) → M,
      _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T (n + 1) v)
      σ (fun v => rfl) ?_
    intro f x y _ hf v
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hf, hswap]

open Polynomial in

theorem _root_.GlobalTheory.PsChar.cayleyHamilton (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : _root_.GlobalTheory.PsChar.IsPsChar d (fun x => T x)) (x : R) :
    ∃ p : Polynomial k, p.Monic ∧ p.natDegree = d ∧ ∀ y : R, T (Polynomial.aeval x p * y) = 0 := by
  have hc : ∀ a b : R, T (a * b) = T (b * a) := h.comm
  have hupd : ∀ (m : ℕ) (i : Fin (m + 1)) (w : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Function.update (fun _ => x) i w) =
        _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons w fun _ => x) := by
    intro m i w
    rw [← pseudo_character_sum_comp_perm _ hc (m + 1) _ (Equiv.swap 0 i)]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Function.comp_apply, Equiv.swap_apply_left, Function.update_self, Fin.cons_zero]
    · rw [Function.comp_apply, Fin.cons_succ, Function.update_of_ne]
      intro hj
      exact Fin.succ_ne_zero _
        ((Equiv.swap 0 i).injective (hj.trans (Equiv.swap_apply_left 0 i).symm))
  have hrec : ∀ (m : ℕ) (y : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 2) (Fin.cons y fun _ => x) =
        T y * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (fun _ => x) -
          (m + 1) * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
            (Fin.cons (y * x) fun _ => x) := by
    intro m y
    rw [pseudo_character_sum_cons_expand]
    simp only [hupd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hcoef : ∀ m : ℕ, ∃ c : ℕ → k,
      (∀ y, _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons y fun _ => x) =
        ∑ j ∈ Finset.range (m + 1), c j * T (y * x ^ j)) ∧
      c m = (-1) ^ m * (m.factorial : k) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => 1, fun y => ?_, by simp⟩
      rw [pseudo_character_sum_cons_expand]
      simp
      exact mul_one (T y)
    | succ m ih =>
      obtain ⟨c, hc1, hc2⟩ := ih
      refine ⟨fun j => if j = 0 then _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
        (fun _ => x) else -((m : k) + 1) * c (j - 1), fun y => ?_, ?_⟩
      · rw [hrec, hc1, Finset.sum_range_succ' _ (m + 1)]
        simp only [Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel, pow_zero, mul_one,
          pow_succ', ← mul_assoc, Finset.mul_sum]
        rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by ring
        · ring
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, hc2, Nat.factorial_succ]
        push_cast
        ring
  obtain ⟨c, hc1, hc2⟩ := hcoef d
  have hzero : ∀ y, ∑ j ∈ Finset.range (d + 1), c j * T (y * x ^ j) = 0 := fun y =>
    (hc1 y).symm.trans (h.alt_eq_zero _)
  have hcd : c d ≠ 0 := by
    rw [hc2]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero d)
  have hdeg : (∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) :=
    Polynomial.degree_sum_fin_lt _
  refine ⟨X ^ d + ∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ), Polynomial.monic_X_pow_add hdeg, ?_,
    fun y => ?_⟩
  · rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  · have e := hzero y
    rw [Finset.sum_range_succ] at e
    simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
      add_mul, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => c i / c d * T (x ^ i * y)) d, hc]
    have hs : ∑ i ∈ Finset.range d, c i / c d * T (x ^ i * y) =
        (∑ i ∈ Finset.range d, c i * T (y * x ^ i)) / c d := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hc]; ring
    rw [hs]
    field_simp
    linear_combination e

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (x : B.Aˣ), B.σ (x : B.A) = x → K'.eta ((overExt φ B ψ hψ hσ).gramDet (x : B.A)) = K.eta (B.gramDet (x : B.A)) := by
  first | exact @GlobalTheory.UnitLemma.Unr.eta_overExt | exact GlobalTheory.UnitLemma.Unr.eta_overExt | (intros; apply GlobalTheory.UnitLemma.Unr.eta_overExt <;> assumption)
end

