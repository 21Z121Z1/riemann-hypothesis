import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZero
section
open scoped Matrix

namespace GlobalTheory.NormSystemVanishing

theorem sum_mem_of_orbit_sums {G H : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] (P : AddSubgroup H) (u : G) (f : G → H) (S : Finset G)
    (hS : ∀ g ∈ S, g * u ∈ S)
    (hP : ∀ g, ∑ j ∈ Finset.range (orderOf u), f (g * u ^ j) ∈ P) :
    ∑ g ∈ S, f g ∈ P := by
  have hn : 0 < orderOf u := orderOf_pos u
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
    · simp
    have hpow : ∀ j, g * u ^ j ∈ S := by
      intro j
      induction j with
      | zero => simpa using hg
      | succ j ihj => rw [pow_succ, ← mul_assoc]; exact hS _ ihj
    have hOS : (Finset.range (orderOf u)).image (fun j => g * u ^ j) ⊆ S := by
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hpow j
    have hgO : g ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j) :=
      Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, by simp⟩
    have hsumO : ∑ y ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j), f y =
        ∑ j ∈ Finset.range (orderOf u), f (g * u ^ j) := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        (mul_left_cancel hij)
    rw [← Finset.sum_sdiff hOS, hsumO]
    refine P.add_mem (ih _ (Finset.sdiff_ssubset hOS ⟨g, hgO⟩) ?_) (hP g)
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    refine ⟨hS y hy.1, fun hyu => hy.2 ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hyu
    refine Finset.mem_image.mpr
      ⟨(j + (orderOf u - 1)) % orderOf u, Finset.mem_range.mpr (Nat.mod_lt _ hn), ?_⟩
    show g * u ^ ((j + (orderOf u - 1)) % orderOf u) = y
    rw [pow_mod_orderOf, pow_add, ← mul_assoc, hj, mul_assoc, ← pow_succ',
      Nat.sub_add_cancel hn, pow_orderOf_eq_one, mul_one]

theorem fixed_of_dvd {O H : Type} [CommRing O] [AddCommGroup H] [Module O H]
    (ψ : Module.End O H) (m : H) {p n : ℕ} (hm : (ψ ^ p) m = m) (h : p ∣ n) :
    (ψ ^ n) m = m := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hm, ih]

theorem exists_stable_exponent {O H : Type} [CommRing O] [IsNoetherianRing O] [AddCommGroup H]
    [Module O H] (M : Submodule O H) (hM : M.FG) (ψ : Module.End O H) (l : ℕ) :
    ∃ a₀ : ℕ, ∀ m ∈ M, ∀ a : ℕ, (ψ ^ l ^ a) m = m → (ψ ^ l ^ a₀) m = m := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM
  have key : ∀ (a : ℕ) (x : M),
      x ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) ↔ (ψ ^ l ^ a) x = x := by
    intro a x
    simp [sub_eq_zero]
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian O M›
    ⟨fun a => LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype), fun a b hab x hx => by
      rw [key] at hx ⊢
      exact fixed_of_dvd ψ _ hx (pow_dvd_pow l hab)⟩
  refine ⟨n, fun m hm a ha => ?_⟩
  rcases le_total a n with h | h
  · exact fixed_of_dvd ψ m ha (pow_dvd_pow l h)
  · have e : LinearMap.ker ((ψ ^ l ^ n - 1).comp M.subtype) =
        LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) := hn a h
    have h1 : (⟨m, hm⟩ : M) ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) := (key a _).mpr ha
    rw [← e] at h1
    exact (key n _).mp h1

theorem eq_zero_of_forall_divisible {O H : Type} [CommRing O] [IsNoetherianRing O]
    [IsLocalRing O] [AddCommGroup H] [Module O H] (M : Submodule O H) (hM : M.FG) (t : O)
    (ht : ¬ IsUnit t) (x : H) (hx : ∀ k : ℕ, ∃ m ∈ M, x = t ^ k • m) : x = 0 := by
  have : Module.Finite O M := Module.Finite.iff_fg.mpr hM
  have hx0 : x ∈ M := by
    obtain ⟨m, hm, e⟩ := hx 0
    simpa [e] using hm
  have hI : Ideal.span {t} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) _ hI
  have hmem : (⟨x, hx0⟩ : M) ∈ (⨅ i : ℕ, (Ideal.span {t}) ^ i • ⊤ : Submodule O M) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨m, hm, e⟩ := hx i
    have he : (⟨x, hx0⟩ : M) = t ^ i • (⟨m, hm⟩ : M) := Subtype.ext (by simpa using e)
    rw [he]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [hbot, Submodule.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

private theorem sum_fibre_units_zmod_pow_eq_of_le {H : Type} [AddCommGroup H] (l : ℕ) [Fact l.Prime]
    (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H)
    (hc : ∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
        c (r + 1) x') (r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ∀ (n : ℕ) (hn : r ≤ n), c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ n))ˣ =>
      ZMod.unitsMap (pow_dvd_pow l hn) x' = x), c n x' := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    simp [Finset.filter_eq']
  | succ n hmn ih =>
    have hcomp : ∀ y : (ZMod (l ^ (n + 1)))ˣ,
        ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y =
          ZMod.unitsMap (pow_dvd_pow l hmn)
            (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y) :=
      fun y => (DFunLike.congr_fun
        (ZMod.unitsMap_comp (pow_dvd_pow l hmn) (pow_dvd_pow l (Nat.le_succ n))) y).symm
    have hmaps : ∀ y ∈ Finset.univ.filter (fun y : (ZMod (l ^ (n + 1)))ˣ =>
        ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y = x),
        Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y ∈
          Finset.univ.filter (fun x' : (ZMod (l ^ n))ˣ => ZMod.unitsMap (pow_dvd_pow l hmn) x' = x) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, by rw [← hcomp]; exact hy.2⟩
    rw [ih, ← Finset.sum_fiberwise_of_maps_to hmaps (c (n + 1))]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [hc n x', Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun y _ => ?_) fun _ _ => rfl
    rw [Finset.mem_filter] at hx'
    constructor
    · intro h
      exact ⟨by rw [hcomp, h]; exact hx'.2, h⟩
    · exact fun h => h.2

theorem sum_tower {H : Type} [AddCommGroup H] (l : ℕ) [Fact l.Prime]
    (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H)
    (hc : ∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
        c (r + 1) x') (r k : ℕ) (x : (ZMod (l ^ r))ˣ) :
    c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + k)))ˣ =>
      ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) x' = x), c (r + k) x' := sum_fibre_units_zmod_pow_eq_of_le l c hc r x (r + k) (Nat.le_add_right r k)

theorem totient_dvd (l : ℕ) [hl : Fact l.Prime] (n s : ℕ) (h : n ≤ s) :
    Nat.totient (l ^ n) ∣ (l - 1) * l ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Nat.totient_prime_pow_succ hl.out, mul_comm (l ^ n)]
    exact mul_dvd_mul_left _ (pow_dvd_pow l (by omega))

theorem unit_pow_eq_one (l : ℕ) [hl : Fact l.Prime] (n s : ℕ) (h : n ≤ s)
    (v : (ZMod (l ^ n))ˣ) : v ^ ((l - 1) * l ^ s) = 1 := by
  obtain ⟨d, hd⟩ := totient_dvd l n s h
  rw [hd, pow_mul, ZMod.pow_totient, one_pow]

theorem unit_pow_ne_one (l : ℕ) [hl : Fact l.Prime] (q : ℕ) (hq : Nat.Coprime q l) (h2 : 2 ≤ q)
    (B n : ℕ) (hB : 0 < B) (hn : q ^ B ≤ n) :
    (ZMod.unitOfCoprime q (Nat.Coprime.pow_right n hq)) ^ B ≠ 1 := by
  intro he
  have hl2 : 2 ≤ l := hl.out.two_le
  have hqB : 2 ≤ q ^ B := le_trans h2 (Nat.le_self_pow hB.ne' q)
  have hlt : q ^ B < l ^ n := lt_of_le_of_lt hn (Nat.lt_pow_self (by omega))
  have h1 := congrArg Units.val he
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow,
    ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem normCompatible_eq_zero : ∀ (O H : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [AddCommGroup H] [Module O H] (l : ℕ) [Fact l.Prime], ¬ IsUnit (l : O) → ∀ (q : ℕ) (hq : Nat.Coprime q l), 2 ≤ q → ∀ (M : Submodule O H), M.FG → ∀ (F : H →ₗ[O] H), (∀ x ∈ M, F x ∈ M) → ∀ (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H), (∀ r x, c r x ∈ M) → (∀ r x, F (c r x) = c r (x * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq))) → (∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ => Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), c (r + 1) x') → ∀ r x, c r x = 0 := by
  intro O H _ _ _ _ _ l _ hl q hq hq2 M hM F _ c hcM hF hc r x
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hFpow : ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ) (j : ℕ),
      (F ^ j) (c r y) = c r (y * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq) ^ j) := by
    intro r y j
    induction j generalizing y with
    | zero => simp
    | succ j ih => rw [pow_succ, Module.End.mul_apply, hF, ih, mul_assoc, ← pow_succ']
  obtain ⟨a₀, ha₀⟩ := exists_stable_exponent M hM (F ^ (l - 1)) l
  have hfix : ∀ s, a₀ ≤ s → ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ),
      (F ^ ((l - 1) * l ^ s)) (c r y) = c r y := by
    intro s hs r y
    have h1 : ((F ^ (l - 1)) ^ l ^ r) (c r y) = c r y := by
      rw [← pow_mul, hFpow, unit_pow_eq_one l r r le_rfl, mul_one]
    have h3 := ha₀ _ (hcM r y) r h1
    rw [← pow_mul] at h3
    exact fixed_of_dvd F _ h3 (mul_dvd_mul_left _ (pow_dvd_pow l hs))
  refine eq_zero_of_forall_divisible M hM (l : O) hl (c r x) fun K => ?_
  obtain ⟨s, hs1, hs2⟩ : ∃ s, a₀ ≤ s ∧ r ≤ s := ⟨max a₀ r, le_max_left _ _, le_max_right _ _⟩
  have hBpos : 0 < (l - 1) * l ^ (s + K) := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  obtain ⟨k, hk⟩ : ∃ k, q ^ ((l - 1) * l ^ (s + K)) ≤ r + k := ⟨_, Nat.le_add_left _ _⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod (l ^ (r + k)))ˣ,
      u = ZMod.unitOfCoprime q (Nat.Coprime.pow_right (r + k) hq) := ⟨_, rfl⟩
  have hmap : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) u =
      ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq) := by
    subst hu
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime,
      ZMod.coe_unitOfCoprime, map_natCast]
  have hw1 : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) (u ^ ((l - 1) * l ^ s)) = 1 := by
    rw [map_pow, hmap, unit_pow_eq_one l r s hs2]
  have hwinv : ∀ (g : (ZMod (l ^ (r + k)))ˣ) (j : ℕ),
      c (r + k) (g * (u ^ ((l - 1) * l ^ s)) ^ j) = c (r + k) g := by
    intro g j
    rw [← pow_mul, hu, ← hFpow]
    exact fixed_of_dvd F _ (hfix s hs1 (r + k) g) (dvd_mul_right _ _)
  have hdvd : orderOf (u ^ ((l - 1) * l ^ s)) ∣ l ^ (r + k) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_assoc, ← pow_add]
    exact unit_pow_eq_one l (r + k) (s + (r + k)) (by omega) u
  have hne : (u ^ ((l - 1) * l ^ s)) ^ l ^ K ≠ 1 := by
    rw [← pow_mul, mul_assoc, ← pow_add, hu]
    exact unit_pow_ne_one l q hq hq2 _ (r + k) hBpos hk
  have hK : l ^ K ∣ orderOf (u ^ ((l - 1) * l ^ s)) := by
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).mp hdvd
    rcases le_or_gt K e with h | h
    · rw [he]; exact pow_dvd_pow l h
    · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (he ▸ pow_dvd_pow l h.le)) hne
  obtain ⟨t, ht⟩ := hK
  have hmem : c r x ∈ (Submodule.map (((l : O) ^ K) • LinearMap.id) M).toAddSubgroup := by
    rw [sum_tower l c hc r k x]
    refine sum_mem_of_orbit_sums _ (u ^ ((l - 1) * l ^ s)) (c (r + k)) _ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, hw1, mul_one] at hg ⊢
      exact hg
    · intro g
      rw [Finset.sum_congr rfl (fun j _ => hwinv g j), Finset.sum_const, Finset.card_range, ht]
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_map]
      refine ⟨(t : O) • c (r + k) g, M.smul_mem _ (hcM _ _), ?_⟩
      rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← Nat.cast_smul_eq_nsmul O,
        Nat.cast_mul, Nat.cast_pow]
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_map] at hmem
  obtain ⟨m, hm, e⟩ := hmem
  exact ⟨m, hm, by simpa using e.symm⟩

end GlobalTheory.NormSystemVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZero
section
open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem one_mem_of_mulClosed_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)),
    (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  intro F K _ _ _ _ m S hS T hT hdet
  classical
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet)
  have hint : IsIntegral F T := by
    have hK : IsIntegral K T := Algebra.IsIntegral.isIntegral T
    exact isIntegral_trans T hK
  have hpow : ∀ n : ℕ, T ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ]; exact hS _ ih _ hT
  have hmul : ∀ q : F[X], T * aeval T q ∈ S := by
    intro q
    rw [aeval_eq_sum_range, Finset.mul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']
    exact S.smul_mem _ (hpow i)
  set p := minpoly F T with hpdef
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hkey : T * aeval T p.divX + algebraMap F _ (p.coeff 0) = 0 := by
    have h0 : aeval T p = 0 := minpoly.aeval F T
    have e : aeval T p = T * aeval T p.divX + algebraMap F _ (p.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add p, mul_comm p.divX X]
      simp only [map_add, map_mul, aeval_X, aeval_C]
    rw [← e, h0]
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero, add_zero] at hkey
    have hq : aeval T p.divX = 0 := by
      exact hTu.mul_right_eq_zero.1 hkey
    have hne : p.divX ≠ 0 := by
      intro h
      rw [divX_eq_zero_iff, hc, map_zero] at h
      exact hp0 h
    have hle := minpoly.degree_le_of_ne_zero F T hne hq
    exact absurd (degree_divX_lt hp0) (not_lt.2 hle)
  have hone : (1 : Matrix (Fin m) (Fin m) K) = (-(p.coeff 0)⁻¹) • (T * aeval T p.divX) := by
    rw [eq_neg_of_add_eq_zero_left hkey, smul_neg, neg_smul, neg_neg, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hc, map_one]
  rw [hone]
  exact S.smul_mem _ (hmul _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique
section
namespace GlobalTheory

open Polynomial

theorem denseRange_of_isAlgClosed_padicAlgCl (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) : DenseRange j := by
  rw [Metric.denseRange_iff]
  intro a δ δpos
  haveI : CharZero Ω := j.charZero
  have hint : IsIntegral ℚ_[l] a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set f : ℚ_[l][X] := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have hi : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have he : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l))
      = (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, he, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨c, -, hc⟩ := hb
  exact ⟨c, by rw [hc, dist_eq_norm]; exact hab⟩

theorem padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l)
      (σ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), (∀ x, σ (j x) = τ (j x)) → σ = τ := by
  intro l _ Ω _ _ j σ τ h
  have hc : ∀ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm (g : PadicAlgCl l →+* PadicAlgCl l)
      fun x => (spectralNorm_eq_of_equiv g x).symm).continuous
  have := (denseRange_of_isAlgClosed_padicAlgCl l Ω j).equalizer (hc σ) (hc τ) (funext h)
  exact AlgEquiv.ext fun x => congrFun this x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate
section
open scoped TensorProduct

namespace GlobalTheory.EmbUnitBallConj

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {ι : Type}
    [Fintype ι] (y : ι → E) (c : ι → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) :
    ∑ k, c k • b (y k) = 0 := by
  haveI : CharZero E := a.charZero
  have hd : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : ι → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : ι → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : ι → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_equiv_of_ker_le {F T K : Type} [Field F] [CommRing T] [Algebra F T] [Field K]
    [Algebra F K] [IsAlgClosed K] [Algebra.IsAlgebraic F K] (f g : T →ₐ[F] K)
    (h : RingHom.ker f ≤ RingHom.ker g) : ∃ σ : K ≃ₐ[F] K, ∀ x, σ (f x) = g x := by
  let S : IntermediateField F K :=
    Subalgebra.IsAlgebraic.toIntermediateField (S := f.range)
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
  let φ : f.range →ₐ[F] K :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)).comp
      (Ideal.quotientKerEquivRange f).symm.toAlgHom
  have hφ : ∀ x, φ ⟨f x, x, rfl⟩ = g x := by
    intro x
    have : (Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩ = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)
      ((Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩) = g x
    rw [this]
    rfl
  let φ' : S →ₐ[F] K := φ
  obtain ⟨ψ, hψ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := F) (L := S) (M := K)
    (E := K) φ'
  refine ⟨AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ), fun x => ?_⟩
  rw [← hφ x]
  exact DFunLike.congr_fun hψ (⟨f x, x, rfl⟩ : S)

noncomputable def ext (a : E →+* PadicAlgCl l) : ℚ_[l] ⊗[ℤ] E →ₐ[ℚ_[l]] PadicAlgCl l :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) a.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem ext_tmul (a : E →+* PadicAlgCl l) (c : ℚ_[l]) (x : E) : ext a (c ⊗ₜ x) = c • a x := by
  simp [ext, Algebra.smul_def, Algebra.ofId_apply]

theorem exists_conj : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] (j₁ j₂ : Ω →+* PadicAlgCl l), (∀ x, ‖j₁ x‖ ≤ 1 ↔ ‖j₂ x‖ ≤ 1) → ∃ σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, σ (j₁ x) = j₂ x := by
  intro l _ Ω _ a b h
  have h' : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have ha : 0 < ‖a x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have hb : 0 < ‖b x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have := h x⁻¹
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_le_one₀ ha, inv_le_one₀ hb] at this
      rw [← not_le, ← not_le, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_of_ker_le (ext a) (ext b) (by
    intro t ht
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
    rw [RingHom.mem_ker, map_sum] at ht ⊢
    simp only [ext_tmul] at ht ⊢
    rw [← Finset.sum_coe_sort] at ht ⊢
    exact sum_eq_zero a b h' _ _ ht)
  refine ⟨σ, fun x => ?_⟩
  simpa [ext_tmul] using hσ (1 ⊗ₜ x)

end GlobalTheory.EmbUnitBallConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowLeSpanPowSup
section
namespace GlobalTheory.SpanPowerSupremum

theorem span_sup_sq_eq {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Q.IsPrime]
    (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ 2) :
    Ideal.span {π} ⊔ Q ^ 2 = Q := by
  have hp : Prime Q := Ideal.prime_of_isPrime hQ ‹_›
  have hle : Ideal.span {π} ⊔ Q ^ 2 ≤ Q :=
    sup_le ((Ideal.span_singleton_le_iff_mem Q).mpr h1) (Ideal.pow_le_self two_ne_zero)
  have hdvd : Ideal.span {π} ⊔ Q ^ 2 ∣ Q ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hp 2).mp hdvd
  have heq : Ideal.span {π} ⊔ Q ^ 2 = Q ^ i := associated_iff_eq.mp hassoc
  interval_cases i
  ·
    rw [pow_zero, Ideal.one_eq_top] at heq
    rw [heq, top_le_iff] at hle
    exact (Ideal.IsPrime.ne_top ‹_› hle).elim
  · rw [pow_one] at heq
    exact heq
  ·
    have hmem : π ∈ Ideal.span {π} ⊔ Q ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
    rw [heq] at hmem
    exact (h2 hmem).elim

theorem pow_le_span_pow_sup {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A}
    [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ (2 : ℕ)) (m : ℕ) :
    Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + (1 : ℕ)) := by
  have hπ : Ideal.span {π} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr h1
  induction m with
  | zero => simp
  | succ m ih =>
    have hπm : Ideal.span {π ^ m} ≤ Q ^ m := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono hπ m
    calc Q ^ (m + 1) = Q ^ m * Q := pow_succ Q m
      _ ≤ (Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) * (Ideal.span {π} ⊔ Q ^ 2) :=
          Ideal.mul_mono ih (span_sup_sq_eq hQ h1 h2).ge
      _ ≤ Ideal.span {π ^ (m + 1)} ⊔ Q ^ (m + 1 + 1) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
            exact le_sup_left
          · refine le_sup_of_le_right ?_
            calc Ideal.span {π ^ m} * Q ^ 2 ≤ Q ^ m * Q ^ 2 := Ideal.mul_mono_left hπm
              _ = Q ^ (m + 1 + 1) := by rw [← pow_add]
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Ideal.span {π} ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right hπ
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Q ^ 2 ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right (Ideal.pow_le_self two_ne_zero)
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm

end GlobalTheory.SpanPowerSupremum
end

