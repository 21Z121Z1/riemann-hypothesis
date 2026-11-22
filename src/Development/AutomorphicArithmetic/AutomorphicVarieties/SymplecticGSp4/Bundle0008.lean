import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0005

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pts_wv {K : Type} [CommRing K] (t : Multiplicative (ℤ × ℤ) →* Kˣ) (w : ℤ × ℤ) :
    wv (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) w = t (Multiplicative.ofAdd w) := by
  obtain ⟨a, b⟩ := w
  have h : Multiplicative.ofAdd ((a, b) : ℤ × ℤ) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) ^ a * Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) ^ b := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_zpow, toAdd_mul, Prod.ext_iff]
  rw [h, map_mul, map_zpow, map_zpow]
  rfl

private theorem pts_abs {O S K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S] [IsCO O S] [Field K] [IsAlgClosed K] [Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (W : WPres O (ℤ × ℤ) S) (hz : ∀ i, W.z i ∈ maximalIdeal S)
    (A B : Subalgebra O S) (hA : W.A = A) [Module.Finite O B] (hB : W.part 0 ≤ B.toSubmodule) (ξ : A →ₐ[O] K) :
    ∃ (t : Kˣ × Kˣ) (y : S →ₐ[O] K), ∀ w, ∀ x : A, (x : S) ∈ W.part w → y x = (wv t w : K) * ξ x := by
  subst hA
  have hB' : IsNoetherian O B.toSubmodule := by
    have : IsNoetherian O B := isNoetherian_of_isNoetherianRing_of_finite O B
    exact this
  have hP : IsNoetherian O (W.part 0) := isNoetherian_of_le hB
  have hG : (W.gr 0).FG := by
    apply Submodule.fg_of_fg_map_injective W.A.val.toLinearMap Subtype.val_injective
    have hle : Submodule.map W.A.val.toLinearMap (W.gr 0) ≤ W.part 0 := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    first
      | exact isNoetherian_submodule.mp hP _ hle
      | exact isNoetherian_submodule'.mp hP _ hle
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite O (ℤ × ℤ) S W hz K ξ (hG.map _)
  refine ⟨(t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))), Ξ, ?_⟩
  intro w x hx
  have hx' : x ∈ W.gr w := hx
  have h1 := act_of_mem W.gr t ξ hx'
  rw [← hΞ] at h1
  rw [pts_wv]
  exact h1

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptScale :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ∃ t r, D.EPt r ∧ ∀ g, r g = tconj t (M.rep ξ g) := by
  intro Ω _ _ _ l _ c D hD M hF ξ
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨hinj, -, -, hcomp, -⟩ := dvrFacts l c.O
  haveI : Algebra.IsAlgebraic ℤ_[l] ℚ_[l] := IsLocalization.isAlgebraic ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) := Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.extendScalars hinj
  obtain ⟨-, -, WS, hWS, hz⟩ := sInternal D hD M
  have hpart : WS.part = M.sPart := funext hWS
  have hA : WS.A = M.SS := by
    simp only [WPres.A, Model.SS, hpart]
  haveI hfin : Module.Finite c.O (Algebra.adjoin c.O (mono M.ru.hom 0)) := hF M.S M.ru M.pt
  have hB : WS.part 0 ≤ (Algebra.adjoin c.O (mono M.ru.hom 0)).toSubmodule := by
    rw [hWS, spanMono D hD M hF 0, Submodule.span_le]
    exact Algebra.subset_adjoin
  obtain ⟨t, y, hy⟩ := pts_abs WS hz M.SS _ hA hB ξ
  refine ⟨t, mapRep (y : M.S →+* PadicAlgCl l) M.ru.hom, ⟨M.S, _, _, _, M.ru, y, M.pt, rfl⟩, ?_⟩
  intro g
  ext i j
  have h := hy (wt i j) (M.ent g i j) (by rw [hWS]; exact M.entry_mem g i j)
  have e : ((M.ent g i j : M.SS) : M.S) = M.ru.hom g i j := rfl
  rw [e] at h
  simpa [tconj, Model.rep, mapRep, Model.rS] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SmoothPtPartOfSmoothPtAssociatedGraded
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private lemma order_pow {O A K τ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [Algebra O K]
    (x : A →ₐ[O] O) (φ : A →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, MvPowerSeries.constantCoeff (φ f) = algebraMap O K (x f)) (n : ℕ) :
    ∀ g ∈ RingHom.ker x ^ n, (n : ℕ∞) ≤ (φ g).order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
    · rw [RingHom.mem_ker] at hb
      rw [map_mul]
      refine le_trans ?_ MvPowerSeries.le_order_mul
      push_cast
      refine add_le_add (ih a ha) (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 ?_)
      rw [hc, hb, map_zero]
    · intro a b ha hb
      rw [map_add]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

private lemma extend {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (A : Subalgebra O R) (q : Ideal R) (φ : A →ₐ[O] MvPowerSeries τ K)
    (ho : ∀ (n : ℕ) (y : A), (y : R) ∈ q ^ n → (n : ℕ∞) ≤ (φ y).order)
    (ha : ∀ (n : ℕ) (x : R), ∃ y : A, x - y ∈ q ^ n) :
    ∃ ψ : R →ₐ[O] MvPowerSeries τ K, ∀ (n : ℕ) (x : R) (y : A), x - y ∈ q ^ n → ∀ m : τ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m (ψ x) = MvPowerSeries.coeff m (φ y) := by
  classical
  choose a ha using ha
  let ψ : R → MvPowerSeries τ K := fun x m => MvPowerSeries.coeff m (φ (a (m.degree + 1) x))
  have spec : ∀ (n : ℕ) (x : R) (y : A), x - y ∈ q ^ n → ∀ m : τ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m (ψ x) = MvPowerSeries.coeff m (φ y) := by
    intro n x y hy m hm
    show MvPowerSeries.coeff m (φ (a (m.degree + 1) x)) = _
    have h1 : x - y ∈ q ^ (m.degree + 1) := Ideal.pow_le_pow_right hm hy
    have h2 : ((a (m.degree + 1) x - y : A) : R) ∈ q ^ (m.degree + 1) := by
      have := Ideal.sub_mem _ h1 (ha (m.degree + 1) x)
      rw [sub_sub_sub_cancel_left] at this
      exact this
    have h3 : MvPowerSeries.coeff m (φ (a (m.degree + 1) x - y)) = 0 := by
      refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (ho _ _ h2))
      exact_mod_cast Nat.lt_succ_self _
    rwa [map_sub, map_sub, sub_eq_zero] at h3
  have onA : ∀ y : A, ψ y = φ y := fun y => by
    ext m
    exact spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)
  have hadd : ∀ x x', ψ (x + x') = ψ x + ψ x' := fun x x' => by
    ext m
    have hm := Nat.lt_succ_self m.degree
    rw [map_add, spec _ x _ (ha _ x) m hm, spec _ x' _ (ha _ x') m hm, ← map_add, ← map_add]
    refine spec _ _ _ ?_ m hm
    have := Ideal.add_mem _ (ha (m.degree + 1) x) (ha (m.degree + 1) x')
    rw [sub_add_sub_comm] at this
    exact this
  have hmul : ∀ x x', ψ (x * x') = ψ x * ψ x' := fun x x' => by
    ext m
    have hm := Nat.lt_succ_self m.degree
    have h1 : x * x' - ((a (m.degree + 1) x * a (m.degree + 1) x' : A) : R) ∈ q ^ (m.degree + 1) := by
      have := Ideal.add_mem _ (Ideal.mul_mem_right x' _ (ha (m.degree + 1) x))
        (Ideal.mul_mem_left _ (a (m.degree + 1) x : R) (ha (m.degree + 1) x'))
      convert this using 1
      push_cast
      ring
    rw [spec _ _ _ h1 m hm, map_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h2 : p.1.degree + p.2.degree = m.degree := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add]
    rw [spec _ x _ (ha (m.degree + 1) x) p.1 (by omega), spec _ x' _ (ha (m.degree + 1) x') p.2 (by omega)]
  refine ⟨{ toFun := ψ
            map_one' := (onA 1).trans (map_one φ)
            map_mul' := hmul
            map_zero' := (onA 0).trans (map_zero φ)
            map_add' := hadd
            commutes' := fun c => (onA (algebraMap O A c)).trans (φ.commutes c) }, spec⟩

theorem UpperTheory.smoothPt_part_of_smoothPt_associatedGraded :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (n : X → ℕ), SmoothPt W.gr (W.originA h) n → SmoothPt W.part (W.origin h) n := by
  rintro O X R _ _ _ _ _ _ _ _ W h n ⟨τ, fτ, wt, φ, H, hn⟩
  obtain ⟨ψ, spec⟩ := extend W.A (RingHom.ker (W.origin h)) φ
    (fun k y hy => order_pow (W.originA h) φ H.const k y (by
      rw [← (ker_pow O R X W h k).1]
      exact hy))
    (fun k => (ker_pow O R X W h k).2)
  have onA : ∀ y : W.A, ψ y = φ y := fun y => by
    ext m
    exact spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)
  obtain ⟨h1, h2⟩ := ker_pow O R X W h 2
  have hx : ∀ (f : R) (y : W.A), f - y ∈ RingHom.ker (W.origin h) ^ 2 → W.origin h f = W.originA h y := by
    intro f y hy
    have := Ideal.pow_le_self (two_ne_zero) hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  refine ⟨τ, fτ, wt, ψ, ⟨fun j f hf => ?_, fun f => ?_, fun i => ?_, fun f hf hl => ?_⟩, hn⟩
  · have := H.graded j ⟨f, W.part_le_A hf⟩ hf
    rw [← onA] at this
    exact this
  · obtain ⟨y, hy⟩ := h2 f
    rw [hx f y hy, ← H.const, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact spec 2 f y hy 0 (by simp)
  · obtain ⟨f, hf, hf'⟩ := H.onto i
    rw [← onA] at hf hf'
    exact ⟨f, hf, hf'⟩
  · obtain ⟨y, hy⟩ := h2 f
    obtain ⟨c, hc, hcy⟩ := H.inj y ((hx f y hy).symm.trans hf) (fun i => by
      rw [← spec 2 f y hy _ (by rw [Finsupp.degree_single]; norm_num)]
      exact hl i)
    rw [← h1] at hcy
    have h3 : c • (y : R) ∈ RingHom.ker (W.origin h) ^ 2 := hcy
    refine ⟨c, hc, ?_⟩
    have h4 := Ideal.add_mem _ (Submodule.smul_of_tower_mem _ c hy) h3
    rwa [← smul_add, sub_add_cancel] at h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SmoothPtWeightedPresentationOfPointDerivations
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem origin_part {O X B : Type} [CommRing O] [AddCommGroup X] [CommRing B] [Algebra O B]
    (W : WPres O X B) (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {x : B} (hx : x ∈ W.part j) :
    W.origin h x = 0 := by
  obtain ⟨F, hF, rfl⟩ := hx
  refine (W.origin_π h F).trans ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hF 0 (by rw [map_zero]; exact hj.symm)

private theorem sep_char {O : Type} [CommRing O] (u : Oˣ) (hu : ¬ IsOfFinOrder u) {i j : ℤ × ℤ} (h : i ≠ j) :
    ∃ t : Multiplicative (ℤ × ℤ) →* Oˣ, t (Multiplicative.ofAdd i) ≠ t (Multiplicative.ofAdd j) := by
  have hinj := injective_zpow_iff_not_isOfFinOrder.2 hu
  by_cases h1 : i.1 = j.1
  · refine ⟨(zpowersHom Oˣ u).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd ℤ ℤ)), fun e => h ?_⟩
    exact Prod.ext h1 (hinj e)
  · exact ⟨(zpowersHom Oˣ u).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ ℤ)), fun e => h1 (hinj e)⟩

private theorem core {O B ι : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B]
    [IsCO O (DualNumber O)] (u : Oˣ) (hu : ¬ IsOfFinOrder u)
    (W : WPres O (ℤ × ℤ) B) (h : W.HasOrigin) (e : ι → B) (w : ι → ℤ × ℤ) (he : ∀ a, e a ∈ W.part (w a))
    (huniq : ∀ f f' : B →ₐ[O] DualNumber O, (∀ a, f (e a) = f' (e a)) → f = f')
    (y : B →ₐ[O] DualNumber O) (j : ℤ × ℤ)
    (h1 : ∀ a, (y (e a)).fst = W.origin h (e a)) (h2 : ∀ a, w a ≠ j → (y (e a)).snd = 0) :
    (∀ x, (y x).fst = W.origin h x) ∧ ∀ i, i ≠ j → ∀ x ∈ W.part i, (y x).snd = 0 := by
  classical
  have hz : ∀ s, W.z s ∈ maximalIdeal B := by
    intro s
    by_contra hs
    have hu' : IsUnit (W.z s) := by
      rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hs
      exact hs
    have h0 : W.origin h (W.z s) = 0 := by
      rw [WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have h3 := hu'.map (W.origin h)
    rw [h0] at h3
    exact not_isUnit_zero h3
  have hmul : ∀ (c : O) (d : DualNumber O), (algebraMap O (DualNumber O) c * d).fst = c * d.fst ∧
      (algebraMap O (DualNumber O) c * d).snd = c * d.snd := by
    intro c d
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact ⟨rfl, rfl⟩
  have hfst : ∀ x, (y x).fst = W.origin h x := by
    have key := huniq ((Algebra.ofId O (DualNumber O)).comp ((TrivSqZeroExt.fstHom O O O).comp y))
      ((Algebra.ofId O (DualNumber O)).comp (W.origin h)) (by
        intro a
        simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, h1 a])
    intro x
    have h4 := congrArg TrivSqZeroExt.fst (AlgHom.congr_fun key x)
    simpa [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl] using h4
  refine ⟨hfst, ?_⟩
  intro i hij x hx
  obtain ⟨s, hs⟩ := sep_char u hu hij
  obtain ⟨y1, hy1, -⟩ := tact O (ℤ × ℤ) B W hz (DualNumber O) y
    ((Units.map (algebraMap O (DualNumber O)).toMonoidHom).comp s)
  have hy1' : ∀ k, ∀ z ∈ W.part k, (y1 z).fst = ↑(s (Multiplicative.ofAdd k)) * (y z).fst ∧
      (y1 z).snd = ↑(s (Multiplicative.ofAdd k)) * (y z).snd := by
    intro k z hz'
    rw [hy1 k z hz']
    exact hmul _ _
  set c : O := ↑(s (Multiplicative.ofAdd j))⁻¹ with hc
  let φ : DualNumber O →ₐ[O] DualNumber O := TrivSqZeroExt.map (c • LinearMap.id)
  have hφ : ∀ d : DualNumber O, (φ d).fst = d.fst ∧ (φ d).snd = c * d.snd := by
    intro d
    exact ⟨TrivSqZeroExt.fst_map _ _, TrivSqZeroExt.snd_map _ _⟩
  have hcj : c * ↑(s (Multiplicative.ofAdd j)) = 1 := Units.inv_mul _
  have heq : φ.comp y1 = y := by
    apply huniq
    intro a
    obtain ⟨ha1, ha2⟩ := hy1' (w a) (e a) (he a)
    obtain ⟨hb1, hb2⟩ := hφ (y1 (e a))
    rw [AlgHom.comp_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hb1, ha1, hfst]
      by_cases hw : w a = 0
      · rw [hw, ofAdd_zero, map_one, Units.val_one, one_mul]
      · rw [origin_part W h hw (he a), mul_zero]
    · rw [hb2, ha2]
      by_cases hw : w a = j
      · rw [hw, ← mul_assoc, hcj, one_mul]
      · rw [h2 a hw, mul_zero, mul_zero]
  have hx1 := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq x)
  rw [AlgHom.comp_apply, (hφ _).2, (hy1' i x hx).2, ← mul_assoc] at hx1
  have hne : c * ↑(s (Multiplicative.ofAdd i)) - 1 ≠ 0 := by
    intro h0
    apply hs
    apply Units.ext
    have h5 : c * ↑(s (Multiplicative.ofAdd i)) = c * ↑(s (Multiplicative.ofAdd j)) := by
      rw [hcj]
      exact sub_eq_zero.mp h0
    exact (Units.isUnit _).mul_left_cancel h5
  have h6 : (c * ↑(s (Multiplicative.ofAdd i)) - 1) * (y x).snd = 0 := by
    rw [sub_mul, one_mul, hx1, sub_self]
  exact (mul_eq_zero.mp h6).resolve_left hne

private theorem ex_unit (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : ∃ u : Oˣ, ¬ IsOfFinOrder u := by
  obtain ⟨hinj, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l O
  have hnd : ¬ l ∣ (l + 1) := by
    intro h
    have h' := (Nat.dvd_add_right (dvd_refl l)).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h')
  obtain ⟨u, hu⟩ := hunit (l + 1) hnd
  refine ⟨u, ?_⟩
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  have h1 : ((l + 1 : ℕ) : O) ^ n = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  have h2 : (((l + 1) ^ n : ℕ) : O) = ((1 : ℕ) : O) := by
    push_cast at h1 ⊢
    exact h1
  rcases Nat.pow_eq_one.mp (Nat.cast_injective h2) with h3 | h3
  · exact hl.out.ne_zero (by omega)
  · exact hn.ne' h3

theorem UpperTheory.smoothPt_weightedPresentation_of_pointDerivations :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (L : LocBase D) (y : L.B →ₐ[c.O] DualNumber c.O) (j : ℤ × ℤ), (∀ (v : D.T) (g : D.Gp v) (a b : Fin 4), (y ((L.ρ v).hom g a b)).fst = D.r0 g a b ∧ (wt a b ≠ j → (y ((L.ρ v).hom g a b)).snd = 0)) → (∀ x, (y x).fst = L.W.origin L.org x) ∧ ∀ i, i ≠ j → ∀ x ∈ L.W.part i, (y x).snd = 0 := by
  intro Ω _ _ _ l _ c D _ L y j H
  haveI := c.dvr
  obtain ⟨u, hu⟩ := ex_unit l c.O
  refine core u hu L.W L.org (ι := (v : D.T) × D.Gp v × Fin 4 × Fin 4)
    (fun a => (L.ρ a.1).hom a.2.1 a.2.2.1 a.2.2.2) (fun a => wt a.2.2.1 a.2.2.2) (fun a => L.hom _ _ _ _) ?_ y j
    (fun a => (H _ _ _ _).1.trans (L.at0 _ _ _ _).symm) (fun a => (H _ _ _ _).2)
  intro f f' hff
  obtain ⟨f0, -, hf0⟩ := L.univ (DualNumber c.O) (fun v => (L.ρ v).map f) (L.eqs.map f)
  refine (hf0 f fun _ => rfl).trans (hf0 f' fun v => ?_).symm
  exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => (hff ⟨v, g, a, b⟩).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem list_neg {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : ((L.map d).sum).2 < 0) :
    ∃ a ∈ L, (d a).2 < 0 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : (d b).2 < 0
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem list_pos {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : 0 < ((L.map d).sum).2) :
    ∃ a ∈ L, 0 < (d a).2 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : 0 < (d b).2
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem span_zero {O S K : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (T : Set S) (hT : ∀ y ∈ T, ∃ h : y ∈ B, ξ ⟨y, h⟩ = 0)
    (x : B) (hx : x.1 ∈ Submodule.span O T) : ξ x = 0 := by
  obtain ⟨x, hxB⟩ := x
  have hx' : x ∈ Submodule.span O T := hx
  clear hx
  suffices H : ∃ h : x ∈ B, ξ ⟨x, h⟩ = 0 by
    obtain ⟨_, h⟩ := H
    exact h
  clear hxB
  induction hx' using Submodule.span_induction with
  | mem y hy => exact hT y hy
  | zero => exact ⟨B.zero_mem, map_zero ξ⟩
  | add y z _ _ hy hz =>
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨B.add_mem hy1 hz1, ?_⟩
    have e : (⟨y + z, B.add_mem hy1 hz1⟩ : B) = ⟨y, hy1⟩ + ⟨z, hz1⟩ := rfl
    rw [e, map_add, hy2, hz2, add_zero]
  | smul a y _ hy =>
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨B.smul_mem hy1 a, ?_⟩
    have e : (⟨a • y, B.smul_mem hy1 a⟩ : B) = a • ⟨y, hy1⟩ := rfl
    rw [e, map_smul, hy2, smul_zero]

private theorem prod_zero {O S K α : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (e : α → B) (L : List α) (a : α) (ha : a ∈ L) (h0 : ξ (e a) = 0) :
    ∃ h : (L.map fun a => (e a).1).prod ∈ B, ξ ⟨_, h⟩ = 0 := by
  have hp : (((L.map e).prod : B) : S) = (L.map fun a => (e a).1).prod := by
    simpa [List.map_map, Function.comp_def] using map_list_prod B.val (L.map e)
  have hm : (L.map fun a => (e a).1).prod ∈ B := by
    rw [← hp]
    exact ((L.map e).prod).2
  refine ⟨hm, ?_⟩
  have e1 : (⟨_, hm⟩ : B) = (L.map e).prod := Subtype.ext hp.symm
  rw [e1, map_list_prod, List.map_map]
  apply List.prod_eq_zero
  simp only [List.mem_map, Function.comp_apply]
  exact ⟨a, ha, h0⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.signs :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ((∀ i j, (wt i j).2 < 0 → ¬ Ge (M.rep ξ) i j) → NegZero M.gr (ξ.comp M.toSS)) ∧ ((∀ i j, 0 < (wt i j).2 → ¬ Ge (M.rep ξ) i j) → PosZero M.gr (ξ.comp M.toSS)) ∧ (PosZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 0 2) ∧ (NegZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 2 0) ∧ ∀ ξ' : M.SS →ₐ[c.O] PadicAlgCl l, Same0 M.gr (ξ.comp M.toSS) (ξ'.comp M.toSS) → (∀ g i, M.rep ξ g i i = M.rep ξ' g i i) ∧ (DiagType (M.rep ξ) → DiagType (M.rep ξ')) := by
  intro Ω _ _ _ l _ c D hD M _ h0 ξ
  have hv : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j, M.rep ζ g i j = ζ (M.ent g i j) := fun _ _ _ _ => rfl
  have hwt : ∀ i j : Fin 4, (wt i j).1 = 0 → True := fun _ _ _ => trivial
  have zero_of : ∀ n : ℤ, ∀ f ∈ M.gr n,
      (∀ L : List (G ℚ Ω × Fin 4 × Fin 4), (L.map fun a => wt a.2.1 a.2.2).sum = ((0 : ℤ), n) →
        ∃ a ∈ L, ξ (M.ent a.1 a.2.1 a.2.2) = 0) → ξ (M.toSS f) = 0 := by
    intro n f hf hL
    have hx := (kerA D hD M).2.2 n f hf
    rw [spanMono D hD M h0] at hx
    apply span_zero M.SS ξ (mono M.ru.hom ((0 : ℤ), n)) _ (M.toSS f) hx
    rintro y ⟨L, hsum, rfl⟩
    obtain ⟨a, ha, hz⟩ := hL L hsum
    exact prod_zero M.SS ξ (fun a => M.ent a.1 a.2.1 a.2.2) L a ha hz
  have from_part : ∀ n : ℤ, ∀ g i j, wt i j = ((0 : ℤ), n) → ∃ f ∈ M.gr n, M.toSS f = M.ent g i j := by
    intro n g i j he
    apply (kerA D hD M).2.1 n (M.ent g i j)
    have := M.entry_mem g i j
    rw [he] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hneg n hn f hf
    rw [AlgHom.comp_apply]
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_neg (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hneg _ _ hlt ⟨a.1, hne⟩
  · intro hpos n hn f hf
    rw [AlgHom.comp_apply]
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_pos (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hpos _ _ hlt ⟨a.1, hne⟩
  · rintro hpos ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part 1 g 0 2 (by decide)
    apply hg
    have := hpos 1 one_pos f hf
    rw [AlgHom.comp_apply, hfx] at this
    exact this
  · rintro hneg ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part (-1) g 2 0 (by decide)
    apply hg
    have := hneg (-1) (by norm_num) f hf
    rw [AlgHom.comp_apply, hfx] at this
    exact this
  · intro ξ' hs
    have key : ∀ x : M.SS, (x : M.S) ∈ M.sPart ((0 : ℤ), 0) → ξ x = ξ' x := by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := (kerA D hD M).2.1 0 x hx
      exact hs f hf
    constructor
    · intro g i
      rw [hv, hv]
      apply key
      have := M.entry_mem g i i
      rwa [show wt i i = ((0 : ℤ), 0) by simp [wt]] at this
    · intro hd i j hij ⟨g, hg⟩ ⟨h, hh⟩
      rw [hv] at hg hh
      have hp : ((M.ent g i j * M.ent h j i : M.SS) : M.S) ∈ M.sPart ((0 : ℤ), 0) := by
        rw [spanMono D hD M h0]
        apply Submodule.subset_span
        refine ⟨[(g, i, j), (h, j, i)], ?_, ?_⟩
        · refine Prod.ext ?_ ?_ <;> simp [wt] <;> ring
        · simp [Model.ent]
      have he := key _ hp
      rw [map_mul, map_mul] at he
      apply mul_ne_zero hg hh
      rw [← he]
      by_cases a : ξ (M.ent g i j) = 0
      · rw [a, zero_mul]
      · have hnot := hd i j hij ⟨g, by rw [hv]; exact a⟩
        have hz : ξ (M.ent h j i) = 0 := by
          by_contra hz
          exact hnot ⟨h, by rw [hv]; exact hz⟩
        rw [hz, mul_zero]
end

