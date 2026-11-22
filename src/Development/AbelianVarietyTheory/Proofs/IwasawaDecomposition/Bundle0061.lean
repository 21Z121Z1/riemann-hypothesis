import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import ReciprocityTheory.DualLattices.Bundle0015
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfTheta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.SecEx

theorem exists_lift {K L S C : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing S] [CommRing C] (q : K →+* S) (T : S →+* C) (hT : Function.Surjective T) (I : Ideal S)
    (hI : I = RingHom.ker T) (f : L →+* C) (hf : ∀ k, f (algebraMap K L k) = T (q k)) :
    ∃ g : L →+* AdicCompletion I S,
      (∀ x, ∃ s, AdicCompletion.evalₐ I 1 (g x) = Ideal.Quotient.mk _ s ∧ T s = f x) ∧
      ∀ k, g (algebraMap K L k) = algebraMap S _ (q k) := by
  subst hI
  letI : Algebra K S := q.toAlgebra
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let e := RingHom.quotientKerEquivOfSurjective hT
  have he : ∀ s, e (Ideal.Quotient.mk _ s) = T s := fun s => rfl
  let f' : L →ₐ[K] S ⧸ RingHom.ker T :=
    { (e.symm : C →+* S ⧸ RingHom.ker T).comp f with
      commutes' := fun k => by
        change e.symm (f (algebraMap K L k)) = Ideal.Quotient.mk _ (q k)
        rw [hf, ← he, RingEquiv.symm_apply_apply] }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f'
  refine ⟨g.toRingHom, fun x => ?_, fun k => ?_⟩
  · obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (RingHom.ker T) 1 (g x))
    refine ⟨s, hs.symm, ?_⟩
    have h1 : AdicCompletion.evalOneₐ (RingHom.ker T) (g x) = e.symm (f x) := congr($hg x)
    rw [← AdicCompletion.factorₐ_evalₐ_one, ← hs] at h1
    rw [← he]
    exact (e.eq_symm_apply).1 h1
  · exact g.commutes k

variable (l : ℕ) [Fact l.Prime]

theorem ker_localizedTheta_eq_span_eisenstein : Per.kerP l = RingHom.ker (Per.θP l) := by
  ext a
  refine ⟨fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one]), fun h => ?_⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers ((l : ℕ) : Per.Ainf l)) a
  have h0 : Per.θP l a = 0 := h
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h0, zero_mul, GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  rw [← hx] at h3
  exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Per.AinfP l) s)).1 h3

theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

theorem θ_surjective : Function.Surjective (Per.θ l) := by
  refine surjective_fontaineTheta fun x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y : ℂ_[l]) (Fact.out : l.Prime).pos
  have hz1 : ‖z‖ ≤ 1 := by
    have := (GlobalTheory.RingBasics.mem_OC _).1 y.2
    rw [← hz, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : l.Prime).ne_zero).1 this
  refine ⟨Ideal.Quotient.mk _ ⟨z, (GlobalTheory.RingBasics.mem_OC _).2 hz1⟩, ?_⟩
  rw [frobenius_def]
  exact (map_pow (Ideal.Quotient.mk _) _ _).symm.trans (congrArg _ (Subtype.ext hz))

theorem fontaineTheta_surjective : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l])‖ ^ n * ‖c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const ‖c‖
    rw [zero_mul] at h
    exact (h.eventually (ge_mem_nhds one_pos)).exists
  obtain ⟨a, ha⟩ := θ_surjective l ⟨(l : ℂ_[l]) ^ n * c, (GlobalTheory.RingBasics.mem_OC _).2 (by rwa [norm_mul, norm_pow])⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  have h1 := congrArg (Per.θP l) hu
  rw [map_mul, map_natCast, map_one] at h1
  refine ⟨u ^ n * algebraMap _ _ a, ?_⟩
  rw [map_mul, map_pow, fontaineTheta_algebraMap₂, ha]
  change Per.θP l u ^ n * ((l : ℂ_[l]) ^ n * c) = c
  rw [← mul_assoc, ← mul_pow, mul_comm _ (l : ℂ_[l]), h1, one_pow, one_mul]

theorem θ_zA (z : ℤ_[l]) :
    (Per.θ l (Per.zA l z) : ℂ_[l]) = ((algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) : Om l) : ℂ_[l]) := by
  let F : ℤ_[l] →+* ℂ_[l] := (algebraMap (Per.OC l) ℂ_[l]).comp ((Per.θ l).comp (Per.zA l))
  let G : ℤ_[l] →+* ℂ_[l] :=
    (algebraMap (Om l) ℂ_[l]).comp ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l]))
  have hF : ∀ w, ‖F w‖ ≤ 1 := fun w => (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l (Per.zA l w)).2
  have hG : ∀ w, ‖G w‖ ≤ 1 := fun w => by
    change ‖((algebraMap ℚ_[l] (Om l) (w : ℚ_[l]) : Om l) : ℂ_[l])‖ ≤ 1
    rw [PadicComplex.norm_extends, PadicAlgCl.norm_extends]
    exact w.2
  change F z = G z
  have hb : ∀ n : ℕ, ‖F z - G z‖ ≤ ‖(l : ℂ_[l])‖ ^ n * 2 := fun n => by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [mul_comm, hw]; ring
    have : F z - G z = (l : ℂ_[l]) ^ n * (F w - G w) := by
      rw [hz]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
    linarith [hF w, hG w]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const 2
  rw [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' h hb))

theorem isUnit_padicIntMap (y : nonZeroDivisors ℤ_[l]) : IsUnit (Per.zP l y) := by
  have h0 : (y : ℤ_[l]) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have h1 := congrArg (Per.zP l) (PadicInt.unitCoeff_spec h0)
  rw [map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.RingBasics.isUnit_l l).pow _)

def qP : ℚ_[l] →+* Per.AinfP l := IsLocalization.lift (isUnit_padicIntMap l)

theorem qP_coe (z : ℤ_[l]) : qP l (z : ℚ_[l]) = Per.zP l z := IsLocalization.lift_eq (isUnit_padicIntMap l) z

theorem algebraMap_eq_fontaineTheta_padicMap (k : ℚ_[l]) :
    algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) k) = Per.θP l (qP l k) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    (j := (algebraMap (Om l) ℂ_[l]).comp (algebraMap ℚ_[l] (Om l)))
    (k := (Per.θP l).comp (qP l)) (RingHom.ext fun z => ?_)) k
  change algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = Per.θP l (qP l (z : ℚ_[l]))
  rw [qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]
  exact ((fontaineTheta_algebraMap₂ l _).trans (θ_zA l z)).symm

theorem exists_isSec (l : ℕ) [Fact l.Prime] : ∃ o : Om l →+* Per.BdRp l, IsSec o := by
  obtain ⟨g, h1, h2⟩ := exists_lift (qP l) (Per.θP l) (fontaineTheta_surjective l) (Per.kerP l) (ker_localizedTheta_eq_span_eisenstein l)
    (algebraMap (Om l) ℂ_[l]) (algebraMap_eq_fontaineTheta_padicMap l)
  obtain ⟨e, he1, he2⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  refine ⟨(e.symm : _ →+* Per.BdRp l).comp g, fun x => ?_, fun z => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := h1 x
    have h3 : Per.ev l 1 (e.symm (g x)) = Ideal.Quotient.mk _ s := by
      rw [← he2, RingEquiv.apply_symm_apply, hs]
    have h4 : e.symm (g x) - algebraMap (Per.AinfP l) (Per.BdRp l) s ∈ Per.FilP l 1 := by
      rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, h3, GlobalTheory.RingIface.ev_alg, sub_self]
    have h5 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h4
    rw [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h5
    exact h5.trans hs'
  · have h3 : e.symm (g (algebraMap ℚ_[l] (Om l) (z : ℚ_[l]))) =
        algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l z)) := by
      rw [h2, qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp, ← he1, RingEquiv.symm_apply_apply]
    exact h3

end GlobalTheory.MemLoc.SecEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem pow_sub_one_pow_congr_geom_sum_pow {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) (x : R) :
    (l : R) ∣ (x ^ l - 1) ^ (l - 1) - (∑ i ∈ Finset.range l, x ^ i) ^ l := by
  have key : (l : Polynomial ℤ) ∣ (Polynomial.X ^ l - 1) ^ (l - 1) -
      (∑ i ∈ Finset.range l, (Polynomial.X : Polynomial ℤ) ^ i) ^ l := by
    set y : Polynomial ℤ := Polynomial.X - 1 with hy
    have hy0 : y ≠ 0 := Polynomial.X_sub_C_ne_zero (1 : ℤ)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl y 1
    have hX : y + 1 = Polynomial.X := by rw [hy]; ring
    rw [hX, one_pow] at hr
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_le).symm⟩
    set s : Polynomial ℤ := ∑ i ∈ Finset.range (k + 1), (Polynomial.X : Polynomial ℤ) ^ i with hs
    have h1 : s * y = Polynomial.X ^ (k + 1) - 1 := geom_sum_mul _ _
    have h2 : s = y ^ k + ((k + 1 : ℕ) : Polynomial ℤ) * r := by
      refine mul_right_cancel₀ hy0 ?_
      rw [h1, hr]; ring
    have h3 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ s - y ^ k := ⟨r, by rw [h2]; ring⟩
    have h4 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ (Polynomial.X ^ (k + 1) - 1) - y ^ (k + 1) :=
      ⟨y * r, by rw [hr]; ring⟩
    have h5 := h3.trans (sub_dvd_pow_sub_pow s (y ^ k) (k + 1))
    have h6 := h4.trans (sub_dvd_pow_sub_pow _ (y ^ (k + 1)) k)
    have h7 := dvd_sub h6 h5
    rw [← pow_mul, ← pow_mul, mul_comm k (k + 1), sub_sub_sub_cancel_right] at h7
    simpa using h7
  simpa [map_sum] using map_dvd (Polynomial.aeval (R := ℤ) x) key

theorem exists_div_prime_pow_dvd {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {l : ℕ} (hl : l.Prime)
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (S : Subalgebra R A) (η z : R)
    (hη : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A η ^ n)
    (hz : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A z ^ n) :
    ∃ w : S, (l : A) * (w : A) = algebraMap R A (η ^ l + l * z) ∧ (l : S) ∣ w ^ l := by
  obtain ⟨g₁, m₁, h₁⟩ := hη l
  obtain ⟨g₂, m₂, h₂⟩ := hη (l * l)
  obtain ⟨g₃, m₃, h₃⟩ := hz l
  have hf : ((l.factorial : ℕ) : A) = (l : A) * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.ne_zero]; push_cast; rfl
  have hb : (((l * l).factorial : ℕ) : A) =
      (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) ^ l * ((l.factorial : ℕ) : A) := by
    rw [← Nat.uniformBell_mul_eq l hl.ne_zero]; push_cast; rfl
  have hg : g₁ ^ l = (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) * g₂ := by
    refine ((hu l).pow l).mul_left_cancel ?_
    rw [← mul_pow, h₁, ← pow_mul, ← h₂, hb]; ring
  let a : S := (((l - 1).factorial : ℕ) : S) * ⟨g₁, m₁⟩
  let b : S := algebraMap R S z
  refine ⟨a + b, ?_, ?_⟩
  · rw [map_add, map_mul, map_pow, map_natCast, ← h₁, hf]
    simp only [a, b]
    push_cast
    ring
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl a b
    have ha : (l : S) ∣ a ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) ^ l * (Nat.uniformBell l l : S) * (((l - 1).factorial : ℕ) : S) *
        ⟨g₂, m₂⟩, Subtype.ext ?_⟩
      simp only [a]
      push_cast
      rw [mul_pow, hg, hf]; ring
    have hb : (l : S) ∣ b ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) * ⟨g₃, m₃⟩, Subtype.ext ?_⟩
      simp only [b]
      push_cast
      rw [← h₃, hf]; ring
    rw [hr]
    exact dvd_add (dvd_add ha hb) ⟨a * b * r, by ring⟩

theorem exists_dividedPower_mem_Acris0 (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ) :
    ∃ g ∈ Per.Acris0 l, ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero).exists_right_inv
  have h : ((n.factorial : ℕ) : Per.AinfP l) * (u * algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n) =
      algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by rw [← mul_assoc, hu, one_mul]
  refine ⟨_, ?_, h⟩
  apply GlobalTheory.RingIface.dividedPower_mem_Acris0 <;> assumption

theorem tm_root_pow (l : ℕ) [Fact l.Prime] (e : Per.Fl l) :
    Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = Per.tm e := by
  rw [← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p (Per.Fl l) l e

theorem exists_mu_pow_div_of_isEps (l : ℕ) [hl : Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  set x := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := tm_root_pow l e
  have hmu : mu e = x ^ l - 1 := by rw [hxl]; rfl
  have hθmu : Per.θ l (x ^ l - 1) = 0 := by
    rw [hxl, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self]
  have hθx : Per.θ l (x - 1) ≠ 0 := by
    rw [hx, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_ne_zero]
    exact he.2
  have hη : Per.θ l (∑ i ∈ Finset.range l, x ^ i) = 0 := by
    rw [← geom_sum_mul, map_mul] at hθmu
    exact (mul_eq_zero.1 hθmu).resolve_right hθx
  obtain ⟨z, hz⟩ := pow_sub_one_pow_congr_geom_sum_pow hl.out x
  have hθz : Per.θ l z = 0 := by
    have h := congrArg (Per.θ l) hz
    have h1 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    rw [map_sub, map_pow, map_pow, hθmu, hη, zero_pow h1, zero_pow hl.out.ne_zero, sub_self, map_mul,
      map_natCast] at h
    refine (mul_eq_zero.1 h.symm).resolve_left ?_
    exact_mod_cast hl.out.ne_zero
  obtain ⟨w, hw, hd⟩ := exists_div_prime_pow_dvd hl.out
    (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (Per.Acris0 l) _ z
    (exists_dividedPower_mem_Acris0 l _ hη) (exists_dividedPower_mem_Acris0 l _ hθz)
  refine ⟨w, ?_, hd⟩
  rw [hw, ← hz, add_sub_cancel, map_pow, hmu]

theorem exists_mu_pow_div : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  intro l hl e he
  have step : ∀ m : ℕ, ∀ e : Per.Fl l, e.untilt = 1 →
      (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1 →
      ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
    intro m
    induction m with
    | zero => exact fun e h1 h2 => absurd h1 h2
    | succ m ih =>
      intro e h1 h2
      by_cases h : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = 1
      · obtain ⟨w, hw, hd⟩ := ih _ h h2
        have hmu : mu e = xi e * mu ((frobeniusEquiv (Per.Fl l) l).symm e) := by
          rw [xi, mu, mu, geom_sum_mul, tm_root_pow]
        refine ⟨algebraMap _ _ (xi e ^ (l - 1)) * w, ?_, ?_⟩
        · rw [hmu, map_mul, mul_pow, ← hw, ← map_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
          ring
        · rw [mul_pow]
          exact hd.mul_left _
      · exact exists_mu_pow_div_of_isEps l e ⟨h1, h⟩
  by_cases h : ∃ m : ℕ, (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1
  · obtain ⟨m, hm⟩ := h
    exact step m e he hm
  · push Not at h
    have h1 : e = 1 := by
      refine Perfection.ext fun n => ?_
      have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm)^[n] e)
      rw [h n, map_one, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at h2
      exact h2.symm.trans (map_one (PreTilt.coeff (O := Per.OC l) (p := l) n)).symm
    have h0 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    refine ⟨0, ?_, by rw [zero_pow hl.out.ne_zero]; exact dvd_zero _⟩
    have hm : mu e = 0 := by
      rw [h1]
      exact sub_eq_zero.2 (map_one (WittVector.teichmuller l))
    rw [hm, map_zero, zero_pow h0]
    simp

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem IsEps.isPrimitiveRoot_untilt {l : ℕ} [hl : Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    IsPrimitiveRoot ((frobeniusEquiv (Per.Fl l) l).symm e).untilt l := by
  have hp : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ^ l = 1 := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p, h.1]
  have ho := orderOf_eq_prime hp h.2
  have := IsPrimitiveRoot.orderOf ((frobeniusEquiv (Per.Fl l) l).symm e).untilt
  rwa [ho] at this

theorem ker_theta_eq_span_xi {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    RingHom.ker (Per.θ l) = Ideal.span {xi e} := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -⟩ :=
    ReciprocityTheory.PGsh.a0 l ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l)
  exact ((hX e (PadicComplexInt.integers l) h.isPrimitiveRoot_untilt).2.2.2 pf hpf).1

theorem theta_eq_zero_iff_xi_dvd (l : ℕ) [Fact l.Prime] :
    ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  intro e h a
  rw [← RingHom.mem_ker, ker_theta_eq_span_xi h, Ideal.mem_span_singleton]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogAdd

open Polynomial

theorem one_add_mul_derivative_trunc {R : Type} [CommRing R] (n : ℕ) (u : R[X]) (hu : u ^ n = 0) :
    (1 + u) * derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (n.factorial : R[X]) * derivative u := by
  have h1 : derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-u) ^ k) * ((n.factorial : R[X]) * derivative u) := by
    rw [derivative_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hd : (k + 1) ∣ n.factorial :=
      Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
    have hc : ((n.factorial / (k + 1) : ℕ) : R[X]) * ((k : R[X]) + 1) = (n.factorial : R[X]) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → R[X]) (Nat.div_mul_cancel hd)
    have hs : derivative ((-1 : R[X]) ^ k) = 0 := by
      rcases neg_one_pow_eq_or R[X] k with h | h <;> simp [h]
    rw [derivative_mul, derivative_mul, hs, derivative_natCast, derivative_pow_succ, ← hc, neg_pow u]
    simp only [map_add, map_natCast, map_one]
    ring
  have h2 : (1 + u) * ∑ k ∈ Finset.range n, (-u) ^ k = 1 := by
    have := mul_neg_geom_sum (-u) n
    rw [sub_neg_eq_add, neg_pow u, hu, mul_zero, sub_zero] at this
    exact this
  rw [h1, ← mul_assoc, h2, one_mul]

theorem trunc_add {R : Type} [CommRing R] (hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R)) (n : ℕ)
    (I : Ideal R) (hI : I ^ n = ⊥) (a b : R) (ha : a ∈ I) (hb : b ∈ I) :
    (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * (a + b + a * b) ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * a ^ (k + 1)) +
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * b ^ (k + 1)) := by
  let F : R[X] → R[X] := fun u => ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)
  let J : Ideal R[X] := I.map (C : R →+* R[X])
  have hJ : ∀ u ∈ J, u ^ n = 0 := by
    intro u hu
    have := Ideal.pow_mem_pow hu n
    rwa [← Ideal.map_pow, hI, Ideal.map_bot, Ideal.mem_bot] at this
  set s : R[X] := C a * X with hs
  set t : R[X] := C b * X with ht
  have hsJ : s ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ ha)
  have htJ : t ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ hb)
  have huJ : s + t + s * t ∈ J := J.add_mem (J.add_mem hsJ htJ) (J.mul_mem_right _ hsJ)
  have e1 : (1 + s) * derivative (F s) = _ := one_add_mul_derivative_trunc n s (hJ _ hsJ)
  have e2 : (1 + t) * derivative (F t) = _ := one_add_mul_derivative_trunc n t (hJ _ htJ)
  have e3 : (1 + (s + t + s * t)) * derivative (F (s + t + s * t)) = _ :=
    one_add_mul_derivative_trunc n _ (hJ _ huJ)
  have hunit : IsUnit (1 + (s + t + s * t)) := IsNilpotent.isUnit_one_add ⟨n, hJ _ huJ⟩
  have hD : derivative (F (s + t + s * t) - F s - F t) = 0 := by
    apply hunit.mul_left_cancel
    rw [derivative_add, derivative_add, derivative_mul (f := s) (g := t)] at e3
    rw [derivative_sub, derivative_sub]
    linear_combination e3 - (1 + t) * e1 - (1 + s) * e2
  have hC : F (s + t + s * t) - F s - F t = C ((F (s + t + s * t) - F s - F t).coeff 0) := by
    ext k
    cases k with
    | zero => simp only [coeff_C_zero]
    | succ k =>
      have h := congrArg (fun p => coeff p k) hD
      simp only [coeff_derivative, coeff_zero] at h
      rw [coeff_C_succ]
      have hu : IsUnit ((k : R) + 1) := by exact_mod_cast hR (k + 1) (Nat.succ_ne_zero k)
      exact (hu.mul_left_eq_zero).1 h
  have h0 : (F (s + t + s * t) - F s - F t).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [F, hs, ht, eval_finsetSum]
  rw [h0, map_zero] at hC
  have h1 := congrArg (eval 1) hC
  simp only [F, hs, ht, eval_sub, eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
    eval_natCast, eval_add, eval_C, eval_X, mul_one, eval_zero] at h1
  linear_combination h1

theorem tm_sub_one_mem (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  apply GlobalTheory.RingIface.alg_mem_kerP
  simp [he]

theorem map_mul_sub_one {M A B : Type} [Monoid M] [CommRing A] [CommRing B] (g : M →* A)
    (f : A →+* B) (e e' : M) :
    f (g (e * e') - 1) = f (g e - 1) + f (g e' - 1) + f (g e - 1) * f (g e' - 1) := by
  simp only [map_sub, map_mul, map_one]
  ring

theorem tm_mul_sub_one (l : ℕ) [Fact l.Prime] (e e' : Per.Fl l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm (e * e') - 1) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) *
          algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) :=
  map_mul_sub_one (WittVector.teichmuller l) _ e e'

theorem log_add : ∀ (l : ℕ) [Fact l.Prime], ∀ (e e' : Per.Fl l) (y y' z : Per.BdRp l),
    e.untilt = 1 → e'.untilt = 1 → Per.IsLog l e y → Per.IsLog l e' y' →
      Per.IsLog l (e * e') z → z = y + y' := by
  intro l _ e e' y y' z he he' hy hy' hz
  refine GlobalTheory.RingIface.ev_ext l _ _ fun n => ?_
  let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Per.AinfP l ⧸ Per.kerP l ^ n) := fun m hm => by
    have := (GlobalTheory.RingBasics.isUnit_nat l m hm).map q
    rwa [map_natCast] at this
  apply (hR _ n.factorial_ne_zero).mul_left_cancel
  rw [map_add, mul_add, GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy n,
    GlobalTheory.CrisIncl.factorial_mul_ev l e' y' he' hy' n,
    GlobalTheory.CrisIncl.factorial_mul_ev l _ z (by rw [map_mul, he, he', mul_one]) hz n]
  have hI : ((Per.kerP l).map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have key := trunc_add hR n _ hI _ _ (Ideal.mem_map_of_mem q (tm_sub_one_mem l e he))
    (Ideal.mem_map_of_mem q (tm_sub_one_mem l e' he'))
  rw [tm_mul_sub_one]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = a at key ⊢
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) = b at key ⊢
  change q _ = q _ + q _
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_add]
  exact key

end GlobalTheory.MemLoc.LogAdd
end

