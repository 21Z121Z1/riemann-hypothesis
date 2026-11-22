import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomain
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.InvRatFun

variable {F : Type} [Field F]

noncomputable def shift (s : F ≃+* F) (t : F) : F[X] →+* F[X] :=
  (Polynomial.compRingHom (X + C t)).comp (Polynomial.mapRingHom (s : F →+* F))

theorem shift_apply (s : F ≃+* F) (t : F) (r : F[X]) :
    shift s t r = (r.map (s : F →+* F)).comp (X + C t) := rfl

theorem natDegree_shift (s : F ≃+* F) (t : F) (r : F[X]) :
    (shift s t r).natDegree = r.natDegree := by
  rw [shift_apply, natDegree_comp, natDegree_X_add_C, mul_one, natDegree_map]

theorem leadingCoeff_shift (s : F ≃+* F) (t : F) (r : F[X]) :
    (shift s t r).leadingCoeff = s r.leadingCoeff := by
  rw [shift_apply, leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
    leadingCoeff_X_add_C, one_pow, mul_one, leadingCoeff_map]
  rfl

theorem shift_eq_zero_iff (s : F ≃+* F) (t : F) (r : F[X]) : shift s t r = 0 ↔ r = 0 := by
  rw [← leadingCoeff_eq_zero, leadingCoeff_shift, map_eq_zero_iff _ s.injective,
    leadingCoeff_eq_zero]

theorem coeff_comp_X_add_C_sub' (P : F[X]) (r : F) (e : ℕ) (hP : P.degree ≤ (e + 1 : ℕ)) :
    (P.comp (X + C r) - P).coeff e = r * (e + 1) * P.coeff (e + 1) := by
  have h1 : P.natDegree ≤ e + 1 := natDegree_le_of_degree_le hP
  have h2 : (hasseDeriv e P).natDegree ≤ 1 := (natDegree_hasseDeriv_le P e).trans (by omega)
  rw [coeff_sub, ← taylor_apply, taylor_coeff, eq_X_add_C_of_natDegree_le_one h2,
    hasseDeriv_coeff, hasseDeriv_coeff]
  simp [add_comm 1 e]
  ring

variable [CharZero F]

theorem natDegree_eq_zero_of_fixed {ι : Type} (s : ι → F ≃+* F) (t : ι → F)
    (h : ¬ ∃ f : F, ∀ g, s g f - f = t g) (r : F[X]) (hr : r ≠ 0)
    (hfix : ∀ g, shift (s g) (t g) r = r) : r.natDegree = 0 := by
  by_contra hn
  obtain ⟨e, he⟩ : ∃ e, r.natDegree = e + 1 := ⟨r.natDegree - 1, by omega⟩
  set c := r.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hr
  have hsc : ∀ g, s g c = c := fun g => by
    rw [hc, ← leadingCoeff_shift (s g) (t g), hfix g]
  apply h
  refine ⟨-r.coeff e / ((e + 1 : F) * c), fun g => ?_⟩
  have key : (shift (s g) (t g) r).coeff e = r.coeff e := by rw [hfix g]
  have hdeg : (r.map (s g : F →+* F)).degree ≤ (e + 1 : ℕ) := by
    rw [degree_map]; exact (degree_le_natDegree).trans (by rw [he])
  have hsub := coeff_comp_X_add_C_sub' (r.map (s g : F →+* F)) (t g) e hdeg
  rw [coeff_sub, ← shift_apply, key, coeff_map, coeff_map] at hsub
  have hlc : r.coeff (e + 1) = c := by rw [hc, leadingCoeff, he]
  rw [hlc] at hsub
  change _ - s g (r.coeff e) = t g * (e + 1) * s g c at hsub
  rw [hsc g] at hsub
  have he1 : (e + 1 : F) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  rw [map_div₀, map_neg, map_mul, hsc g, map_add, map_natCast, map_one]
  field_simp
  linear_combination hsub

end GlobalTheory.InvRatFun

namespace GlobalTheory.InvRatFun

variable {F : Type} [Field F] [CharZero F]

theorem dvd_shift_mul {s : F ≃+* F} {t : F} {P Q r : F[X]} (hQ : Q ≠ 0)
    (hPQ : Q * shift s t P = shift s t Q * P) (hr : Q ∣ r * P) : Q ∣ shift s t r * P := by
  obtain ⟨w, hw⟩ := map_dvd (shift s t) hr
  rw [map_mul] at hw
  have hAQ : shift s t Q ≠ 0 := (shift_eq_zero_iff s t Q).not.mpr hQ
  refine ⟨w, ?_⟩
  apply mul_left_cancel₀ hAQ
  linear_combination (-(shift s t r)) * hPQ + Q * hw

theorem eq_C_mul_of_fixed {ι : Type} (s : ι → F ≃+* F) (t : ι → F)
    (h : ¬ ∃ f : F, ∀ g, s g f - f = t g) (P Q : F[X]) (hQ : Q ≠ 0)
    (hPQ : ∀ g, Q * shift (s g) (t g) P = shift (s g) (t g) Q * P) :
    ∃ c : F, P = C c * Q ∧ ∀ g, s g c = c := by
  classical
  have hex : ∃ n, ∃ r : F[X], r.Monic ∧ r.natDegree = n ∧ Q ∣ r * P :=
    ⟨_, Q * C Q.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hQ, rfl,
      ⟨C Q.leadingCoeff⁻¹ * P, by ring⟩⟩
  obtain ⟨q₀, hm, hdeg, hdvd⟩ := Nat.find_spec hex
  have hfix : ∀ g, shift (s g) (t g) q₀ = q₀ := by
    intro g
    set A := shift (s g) (t g)
    have hAm : (A q₀).Monic := by rw [shift_apply]; exact (hm.map _).comp_X_add_C _
    by_contra hne
    have hr : A q₀ - q₀ ≠ 0 := sub_ne_zero.mpr hne
    have hlt : (A q₀ - q₀).degree < (A q₀).degree :=
      degree_sub_lt (by rw [degree_eq_natDegree hAm.ne_zero, degree_eq_natDegree hm.ne_zero,
        natDegree_shift]) hAm.ne_zero (by rw [hAm.leadingCoeff, hm.leadingCoeff])
    have hlt' : (A q₀ - q₀).natDegree < Nat.find hex := by
      rw [← hdeg, ← natDegree_shift (s g) (t g) q₀]; exact natDegree_lt_natDegree hr hlt
    have hd : Q ∣ (A q₀ - q₀) * P := by
      rw [sub_mul]; exact dvd_sub (dvd_shift_mul hQ (hPQ g) hdvd) hdvd
    refine Nat.find_min hex hlt' ⟨(A q₀ - q₀) * C (A q₀ - q₀).leadingCoeff⁻¹,
      monic_mul_leadingCoeff_inv hr,
      natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hr)), ?_⟩
    rw [mul_right_comm]; exact dvd_mul_of_dvd_left hd _
  have h0 := natDegree_eq_zero_of_fixed s t h q₀ hm.ne_zero hfix
  have hq1 : q₀ = 1 := by
    have h1 : q₀.coeff 0 = 1 := by rw [← h0]; exact hm
    rw [eq_C_of_natDegree_eq_zero h0, h1, C_1]
  rw [hq1, one_mul] at hdvd
  obtain ⟨S, rfl⟩ := hdvd
  have hSfix : ∀ g, shift (s g) (t g) S = S := by
    intro g
    have hAQ : shift (s g) (t g) Q ≠ 0 := (shift_eq_zero_iff _ _ Q).not.mpr hQ
    have := hPQ g
    rw [map_mul] at this
    apply mul_left_cancel₀ (mul_ne_zero hQ hAQ)
    linear_combination this
  by_cases hS : S = 0
  · exact ⟨0, by simp [hS], fun g => map_zero _⟩
  have hS0 := natDegree_eq_zero_of_fixed s t h S hS hSfix
  refine ⟨S.leadingCoeff, ?_, fun g => ?_⟩
  · conv_lhs => rw [eq_C_of_natDegree_eq_zero hS0]
    rw [leadingCoeff, hS0, mul_comm]
  · rw [← leadingCoeff_shift (s g) (t g), hSfix g]

end GlobalTheory.InvRatFun

namespace GlobalTheory.InvRatFun

theorem fixed_ratio_const_of {B G : Type} (F : Type) [Field F] [CommRing B] [IsDomain B] [CharZero B] [Algebra B F] [IsFractionRing B F]
    (σ : G → B ≃+* B) (τ : G → B)
    (hτ : ∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g)
    (p q : Polynomial B) (hq : q ≠ 0)
    (hpq : ∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) =
      (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) :
    ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  classical
  have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  haveI : CharZero F := charZero_of_injective_algebraMap hinj
  have hι0 : ∀ x : B, x ≠ 0 → (algebraMap B F) x ≠ 0 := fun x hx => by
    rwa [Ne, ← map_zero (algebraMap B F), hinj.eq_iff]
  let s : G → F ≃+* F := fun g => IsFractionRing.ringEquivOfRingEquiv (σ g)
  have hs : ∀ g x, s g ((algebraMap B F) x) = (algebraMap B F) (σ g x) := fun g x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (σ g) x
  have hcomp : ∀ g, (algebraMap B F).comp (σ g : B →+* B) = (s g : F →+* F).comp (algebraMap B F) := fun g =>
    RingHom.ext fun x => (hs g x).symm
  have hmap : ∀ g (r : B[X]), ((r.map (σ g : B →+* B)).comp (X + C (τ g))).map (algebraMap B F) =
      shift (s g) ((algebraMap B F) (τ g)) (r.map (algebraMap B F)) := by
    intro g r
    rw [shift_apply, Polynomial.map_comp, Polynomial.map_map, Polynomial.map_map, hcomp g]
    simp

  have h : ¬ ∃ f : F, ∀ g, s g f - f = (algebraMap B F) (τ g) := by
    rintro ⟨f, hf⟩
    obtain ⟨d', d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) f
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    apply hτ d d' hd0
    intro g
    have e := hf g
    have h1 := hι0 d hd0
    have h2 := hι0 (σ g d) ((map_ne_zero_iff _ (σ g).injective).mpr hd0)
    rw [map_div₀, hs, hs] at e
    apply hinj
    simp only [map_sub, map_mul]
    field_simp at e
    linear_combination e
  have hQ : q.map (algebraMap B F) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hq
  obtain ⟨c, hc, hcs⟩ := eq_C_mul_of_fixed s (fun g => (algebraMap B F) (τ g)) h (p.map (algebraMap B F)) (q.map (algebraMap B F)) hQ
    (fun g => by
      have e := congrArg (Polynomial.map (algebraMap B F)) (hpq g)
      rwa [Polynomial.map_mul, Polynomial.map_mul, hmap, hmap] at e)
  obtain ⟨d', d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) c
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have h1 := hι0 d hd0
  refine ⟨d, d', hd0, ?_, fun g => ?_⟩
  · apply Polynomial.map_injective (algebraMap B F) hinj
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hc, ← mul_assoc,
      ← C_mul, mul_div_cancel₀ _ h1]
  · have e := hcs g
    have h2 := hι0 (σ g d) ((map_ne_zero_iff _ (σ g).injective).mpr hd0)
    rw [map_div₀, hs, hs] at e
    apply hinj
    simp only [map_mul]
    field_simp at e
    linear_combination e

theorem fixed_ratio_const {B G : Type} [CommRing B] [IsDomain B] [CharZero B]
    (σ : G → B ≃+* B) (τ : G → B)
    (hτ : ∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g)
    (p q : Polynomial B) (hq : q ≠ 0)
    (hpq : ∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) =
      (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) :
    ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' :=
  fixed_ratio_const_of (FractionRing B) σ τ hτ p q hq hpq

end GlobalTheory.InvRatFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopXiInv

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc

theorem xiTop_invariant : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word), Pr.Ok → R.m = m2 + 2 → cst.Ok → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u), Y ∈ ybSet sel mu cst p.deco.1.N → ∀ x z, z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst m2 p Y p' (x + z) = XiTop Ch sel mu cst m2 p Y p' x := by
  classical
  intro X Pr R Ch sel S mu cst m2 u hPr hm hc hD p Y p' hY x y hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  set c : ℕ := cBof sel mu cst u with hcdef
  change XiTop Ch sel mu cst m2 p Y p' (x + (c : 𝓞 X.E) • y₀) = _
  unfold XiTop
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) x = x'
    have hz : ∀ v : Sp X.E (R.N (m2 + 1)), (∀ l, IntAt P.1 (v l)) → ∀ l,
        IntAt P.1 (inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l / (qOf P.1 : X.E) ^ cst.B) := by
      intro v hv l
      have h1 : frsF sel mu p P v ∈ p.deco.1.at P.1 := (frsF_mem p P v).2 ((mem_localization_standardLattice _ _).2 hv)
      have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
      have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) ∈ stdAt X.E _ P.1 := by
        refine (frsF_mem p' P _).1 ?_
        rw [LinearEquiv.apply_symm_apply]
        exact h2
      have h4 := (mem_localization_standardLattice _ _).1 h3 l
      obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
      have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l =
          (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) l := by
        change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P v)) l = _
        rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
      rw [h5, hc']
      convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
      push_cast
      field_simp
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) = z at hz ⊢
    unfold locTop
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.PhiTop_add mu Ch _ _ hm P.1 _ _ fun s l => ?_
      have h1 := hz (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1)) fun l' =>
        GlobalTheory.TopInv.single_int s _
      have h2 := GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos (h1 (Br.iC (N_m_succ R) l))
      rw [pow_one] at h2
      exact h2
    · refine GlobalTheory.TopInv.ftY_add sel mu cst hc P (hD P) _ _ _ (fun s => ?_) ?_
      · exact GlobalTheory.TopInv.atNL_int (R.N R.m - 1) _ _ (hz (Pi.single s 1) (GlobalTheory.TopInv.single_int s))
      · have h1 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
        have h2 := (frsF_mem p P ((frsF sel mu p P).symm
          (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Y))).1 (by
            rw [LinearEquiv.apply_symm_apply]
            exact h1)
        intro l
        have h3 := (mem_localization_standardLattice _ _).1 h2 l
        rw [map_smul] at h3
        exact h3

end GlobalTheory.TopXiInv
end
end

