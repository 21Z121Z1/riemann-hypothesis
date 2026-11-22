import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0164
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushCentre
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem genMap_fromSpec {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) :
    spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 = ξ := by
  have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
  have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 : spMap (genMap ξ q) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
    rw [← Spec.map_comp]
    rfl
  rw [e2, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4

theorem genMap_bij {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (h : IsCptGen ξ) (q : Cpt ξ) (e : q.1 = genPt ξ) :
    Function.Bijective (genMap ξ q) := by
  obtain ⟨p, hp⟩ := q
  subst e
  have : X.presheaf.stalkSpecializes hp = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  simp only [this]
  exact h.bij

theorem genIso : GenIso := by
  intro X Ω Ω' _ _ ξ ξ' h h' e
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  let q' : Cpt ξ' := ⟨genPt ξ, e ▸ specializes_rfl⟩
  let a := RingEquiv.ofBijective _ (genMap_bij h q rfl)
  let a' := RingEquiv.ofBijective _ (genMap_bij h' q' e)
  refine ⟨a'.symm.trans a, ?_⟩
  have hc : (a'.symm.trans a).toRingHom.comp (genMap ξ' q') = genMap ξ q := by
    ext x
    show a (a'.symm (a' x)) = a x
    rw [a'.symm_apply_apply]
  have h1 := genMap_fromSpec ξ q
  have h2 := genMap_fromSpec ξ' q'
  rw [← hc] at h1
  calc ξ = _ := h1.symm
    _ = spMap (a'.symm.trans a).toRingHom ≫ spMap (genMap ξ' q') ≫ X.fromSpecStalk q'.1 := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    _ = _ := by rw [h2]

theorem seg_ratio {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (ch : ∀ k, J k) (h : ∏ k, y ⟨k, ch k⟩ ≠ 0) (k : K) (j : J k) :
    (∏ k', y ⟨k', Function.update ch k j k'⟩) / ∏ k', y ⟨k', ch k'⟩ = y ⟨k, j⟩ / y ⟨k, ch k⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)] at h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun k' => y ⟨k', ch k'⟩) (Finset.mem_univ k),
    Function.update_self, Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')],
    mul_div_mul_right _ _ (right_ne_zero_of_mul h)]

theorem chartVal : ChartVal := by
  intro X Ω Ω₃ _ _ O i ξ q K _ J _ y ch a hD hc
  classical
  unfold vdeg
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow₀, map_zpow₀]
  congr 1
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j => O.valuation (i (y ⟨k, j⟩))) (Finset.mem_univ _))
  have h0 : y ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _)
  have h1 := hD.1 _ (hc.2 (Function.update ch k j))
  rw [seg_ratio y ch hc.1, ← O.valuation_le_one_iff, map_div₀, map_div₀,
    div_le_one₀ (zero_lt_iff.2 (by simpa using h0))] at h1
  exact h1

theorem dom_of_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) (ha : ∀ q : X, genPt ξ ⤳ q) (z : Sp O ⟶ X) (hz : spMap O.subtype ≫ z = spMap i ≫ ξ) :
    ∃ q : Cpt ξ, Dom O i ξ q := by
  let q : Cpt ξ := ⟨z (IsLocalRing.closedPoint O), ha _⟩
  let φ : X.presheaf.stalk q.1 →+* O := (Scheme.stalkClosedPointTo z).hom
  have hl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have e1 : spMap φ ≫ X.fromSpecStalk q.1 = z := Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have e2 : spMap (O.subtype.comp φ) = spMap (i.comp (genMap ξ q)) := by
    rw [← cancel_mono (X.fromSpecStalk q.1)]
    calc _ = spMap O.subtype ≫ spMap φ ≫ X.fromSpecStalk q.1 := by
          rw [← Category.assoc, ← Spec.map_comp]; rfl
      _ = spMap i ≫ spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [e1, genMap_fromSpec, hz]
      _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl
  have e3 : ∀ s, ((φ s : O) : Ω₃) = i (genMap ξ q s) := fun s =>
    congrArg (fun f => f.hom s) (Spec.map_injective e2)
  refine ⟨q, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← e3]
    exact (φ s).2
  · rintro _ ⟨s, rfl⟩ h0 h1
    have hu : IsUnit (φ s) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
      show ((φ s : O) : Ω₃) * _ = 1
      rw [e3, mul_inv_cancel₀ ((map_ne_zero i).2 h0)]))
    obtain ⟨t, ht⟩ := (hl.1 s hu).exists_right_inv
    refine ⟨t, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← map_mul, ht, map_one]

theorem exists_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {κ : Type} (x : κ → Ω) (ht : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (hO : ∀ j, i (x j / x c) ∈ O) :
    ∃ z : Sp O ⟶ X, spMap O.subtype ≫ z = spMap i ≫ ξ := by
  obtain ⟨U, hU, hm⟩ := ht.affine c hc
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hq : q.1 ∈ U := (hm _).2 ⟨q.2, hc, fun c' => (genMap_bij ht.gen q rfl).2 _⟩
  let φ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hq).hom
  have h1 : ∀ s, i (φ s) ∈ O := fun s => by
    have : φ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := (ht.ring c hc _).2 fun p hp => by
      have hpU : p.1 ∈ U := (hm _).2 ⟨p.2, hp⟩
      refine ⟨X.presheaf.germ U p.1 hpU s, ?_⟩
      show Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes p.2 _) =
        Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes q.2 _)
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
    generalize φ s = a at this
    induction this using Algebra.adjoin_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hO j
    | algebraMap n => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let ψ : Γ(X, U) →+* O := (i.comp φ).codRestrict O.toSubring h1
  refine ⟨spMap ψ ≫ hU.fromSpec, ?_⟩
  have e : Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec = X.fromSpecStalk q.1 := hU.fromSpecStalk_eq_fromSpecStalk hq
  calc _ = spMap i ≫ spMap (genMap ξ q) ≫ Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec := by
        simp only [← Category.assoc, ← Spec.map_comp]
        rfl
    _ = _ := by rw [e, genMap_fromSpec]

theorem exists_dom {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ha : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) : ∃ q : Cpt ξ, Dom O i ξ q := by
  obtain ⟨c₀, hc₀, -⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
  have hm : ∀ k, ∃ j : J k, ∀ j', O.valuation (i (y ⟨k, j'⟩)) ≤ O.valuation (i (y ⟨k, j⟩)) := fun k => by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => O.valuation (i (y ⟨k, j⟩))) ⟨c₀ k, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose ch hch using hm
  have hp : ∀ k, 0 < O.valuation (i (y ⟨k, ch k⟩)) := fun k =>
    lt_of_lt_of_le (zero_lt_iff.2 (by simpa using Finset.prod_ne_zero_iff.1 hc₀ k (Finset.mem_univ _))) (hch k (c₀ k))
  have h0 : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k h => by simpa [h] using hp k
  obtain ⟨z, hz⟩ := exists_point O i ξ _ ht ch (Finset.prod_ne_zero_iff.2 fun k _ => h0 k) fun j => by
    rw [← Finset.prod_div_distrib, map_prod]
    refine prod_mem fun k _ => ?_
    rw [← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (hp k)]
    exact hch k (j k)
  exact dom_of_point O i ξ ha z hz

theorem centre : Centre := by
  intro E _ _ _ H D l Xo c Y S S' Ω Ω' Ω₃ _ _ _ K K' _ _ J J' _ _ y y' 𝔐 𝔐' i i' W hξ
  obtain ⟨q, hq⟩ := exists_dom W i 𝔐.ξ y 𝔐.all 𝔐.tie
  obtain ⟨q', hq'⟩ := exists_dom W i' 𝔐'.ξ y' 𝔐'.all 𝔐'.tie
  refine ⟨q, q', hq, hq', ?_⟩
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W i q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐'.ξ W i' q' (𝔐'.tie.gen.inj q') hq'
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐'.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    simpa only [Category.assoc] using hξ
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐'.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐'.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐'.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLinkA
section
noncomputable section

namespace SheetDecomposition

open GlobalTheory.CompanionTheory.Ar

section

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem mem_flagStep_iff (f : Fin r → V) (n : ℕ) (x : V) :
    x ∈ flagStep Ω f n ↔ ∃ B : Fin r → Ω, (∀ m : Fin r, n ≤ (m : ℕ) → B m = 0) ∧ x = ∑ m, B m • f m := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨Pi.single k 1, fun m hm => ?_, ?_⟩
      · have : m ≠ k := by rintro rfl; exact absurd hk (not_lt.2 hm)
        simp [this]
      · simp [Pi.single_apply]
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨B, hB, rfl⟩ := hx
      obtain ⟨C, hC, rfl⟩ := hy
      exact ⟨B + C, fun m hm => by simp [hB m hm, hC m hm], by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul a x _ hx =>
      obtain ⟨B, hB, rfl⟩ := hx
      exact ⟨a • B, fun m hm => by simp [hB m hm], by simp [Finset.smul_sum, mul_smul]⟩
  · rintro ⟨B, hB, rfl⟩
    refine Submodule.sum_mem _ fun m _ => ?_
    by_cases h : (m : ℕ) < n
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, h, rfl⟩)
    · simp [hB m (not_lt.1 h)]

theorem coeff_zero_of_mem {f : Fin r → V} (hf : LinearIndependent Ω f) {n : ℕ} {a : Fin r → Ω}
    (h : ∑ m, a m • f m ∈ flagStep Ω f n) (m : Fin r) (hm : n ≤ (m : ℕ)) : a m = 0 := by
  obtain ⟨B, hB, e⟩ := (mem_flagStep_iff f n _).1 h
  have := Fintype.linearIndependent_iff.1 hf (a - B) (by simp [sub_smul, Finset.sum_sub_distrib, e]) m
  simpa [hB m hm] using this

theorem smul_mem_flagStep {f : Fin r → V} (hf : LinearIndependent Ω f) {m : Fin r} {t : Ω}
    (h : t • f m ∈ flagStep Ω f m) : t = 0 := by
  classical
  have := coeff_zero_of_mem hf (a := Pi.single m t) (n := m) (by simpa [Pi.single_apply] using h) m le_rfl
  simpa using this

theorem sum_sub_mem (f : Fin r → V) (m : Fin r) {B : Fin r → Ω} (hB : ∀ m' : Fin r, (m : ℕ) + 1 ≤ (m' : ℕ) → B m' = 0) :
    ∑ m', B m' • f m' - B m • f m ∈ flagStep Ω f m := by
  classical
  refine (mem_flagStep_iff f m _).2 ⟨B - Pi.single m (B m), fun m' hm' => ?_, ?_⟩
  · by_cases e : m' = m
    · simp [e]
    · have : (m' : ℕ) ≠ m := fun h => e (Fin.ext h)
      simp [e, hB m' (by omega)]
  · simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply]

theorem self_mem_flagStep (f : Fin r → V) (m : Fin r) : f m ∈ flagStep Ω f (m + 1) :=
  Submodule.subset_span ⟨m, Nat.lt_succ_self _, rfl⟩

theorem flagStep_mono (f : Fin r → V) {n n' : ℕ} (h : n ≤ n') : flagStep Ω f n ≤ flagStep Ω f n' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem exists_lead (f : Fin r → V) (m : Fin r) {x : V} (hx : x ∈ flagStep Ω f (m + 1)) :
    ∃ t : Ω, x - t • f m ∈ flagStep Ω f m := by
  obtain ⟨B, hB, rfl⟩ := (mem_flagStep_iff f _ _).1 hx
  exact ⟨B m, sum_sub_mem f m hB⟩

theorem gr_span {b₀ bb : Fin r → V} (h₀ : LinearIndependent Ω b₀) (hb : LinearIndependent Ω bb)
    (hf : ∀ n, flagStep Ω bb n = flagStep Ω b₀ n) (R : Subring Ω) (m : Fin r) {t : Ω}
    (ht : bb m - t • b₀ m ∈ flagStep Ω b₀ m) :
    t ≠ 0 ∧ Submodule.span R {t' : Ω | ∃ e ∈ Submodule.span R (Set.range bb), e - t' • b₀ m ∈ flagStep Ω b₀ m} =
      Submodule.span R {t} := by
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro rfl
    have : (1 : Ω) • bb m ∈ flagStep Ω bb m := by simpa [hf] using ht
    exact one_ne_zero (smul_mem_flagStep hb this)
  · rintro t' ⟨e, he, h⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    have e1 : ∑ l, a l • bb l = ∑ l, (a l : Ω) • bb l := rfl
    rw [e1] at h
    have h1 : ∑ l, (a l : Ω) • bb l ∈ flagStep Ω bb (m + 1) := by
      rw [hf]
      have := Submodule.add_mem _ (flagStep_mono b₀ (Nat.le_succ _) h)
        (Submodule.smul_mem _ t' (self_mem_flagStep (Ω := Ω) b₀ m))
      simpa using this
    have h2 := sum_sub_mem bb m (B := fun l => (a l : Ω)) (coeff_zero_of_mem hb h1)
    rw [hf] at h2
    have h3 : (t' - a m * t) • b₀ m ∈ flagStep Ω b₀ m := by
      have := Submodule.sub_mem _ (Submodule.add_mem _ h2 (Submodule.smul_mem _ (a m : Ω) ht)) h
      convert this using 1
      simp only [sub_smul, smul_sub, mul_smul]
      abel
    have h4 := smul_mem_flagStep h₀ h3
    exact Submodule.mem_span_singleton.2 ⟨a m, by
      show (a m : Ω) * t = t'
      linear_combination -h4⟩
  · rintro _ rfl
    exact Submodule.subset_span ⟨bb m, Submodule.subset_span ⟨m, rfl⟩, ht⟩

end

section

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃)

theorem det_mul_rows {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) :
    (H * G).det = ∑ I : Fin n → Fin r, (∏ a, H a (I a)) * (Matrix.of fun a b => G (I a) b).det := by
  have e : (H * G : Matrix (Fin n) (Fin n) Ω₃) = fun a => ∑ l, H a l • G l := by
    funext a b
    simp [Matrix.mul_apply]
  have h := (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap.map_sum (fun a l => H a l • G l)
  have h' : (H * G).det = (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap (fun a => ∑ l, H a l • G l) := by
    rw [e]; rfl
  rw [h', h]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem sup_minor_eq_one {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) (hH : ∀ a l, H a l ∈ O)
    (hG : ∀ l b, G l b ∈ O) (h : H * G = 1) :
    (Finset.univ.sup fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) = 1 := by
  refine le_antisymm (Finset.sup_le fun I _ => (O.valuation_le_one_iff _).2 ?_) ?_
  · rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => hG _ _)
  · have e := det_mul_rows H G
    rw [h, Matrix.det_one] at e
    rw [← O.valuation.map_one, e]
    refine Valuation.map_sum_le _ fun I _ => ?_
    rw [map_mul]
    refine (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (prod_mem fun a _ => hH _ _))).trans ?_
    exact Finset.le_sup (f := fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) (Finset.mem_univ I)

theorem mul_sup {ι : Type} [Fintype ι] (γ : O.ValueGroup) (f : ι → O.ValueGroup) :
    γ * Finset.univ.sup f = Finset.univ.sup fun I => γ * f I :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => γ * x) (fun _ _ h => mul_le_mul_right h γ)
    (by rw [show (⊥ : O.ValueGroup) = 0 from le_antisymm bot_le zero_le']; exact mul_zero γ)

theorem val_le_of_mem_span {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {S : Set Ω}
    {γ : O.ValueGroup} (hS : ∀ s ∈ S, O.valuation (i s) ≤ γ) {x : Ω} (hx : x ∈ Submodule.span R S) :
    O.valuation (i x) ≤ γ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    show O.valuation (i ((a : Ω) * x)) ≤ γ
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (hR _ a.2))).trans hx

theorem val_eq_of_span_eq {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {x y : Ω}
    (h : Submodule.span R {x} = Submodule.span R {y}) : O.valuation (i x) = O.valuation (i y) :=
  le_antisymm (val_le_of_mem_span O i R hR (S := {y}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self x))
    (val_le_of_mem_span O i R hR (S := {x}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self y))

theorem prod_castLE {M : Type} [CommMonoid M] {r : ℕ} (m : Fin r) (f : Fin r → M) :
    ∏ a : Fin (m + 1), f (Fin.castLE m.2 a) = ∏ m' ∈ Finset.Iic m, f m' := by
  refine Finset.prod_bij (fun a _ => Fin.castLE m.2 a) (fun a _ => ?_) (fun a _ b _ h => Fin.castLE_injective _ h)
    (fun b hb => ⟨⟨b, ?_⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  · exact Finset.mem_Iic.2 (Fin.le_def.2 (Nat.lt_succ_iff.1 a.2))
  · exact Nat.lt_succ_iff.2 (Fin.le_def.1 (Finset.mem_Iic.1 hb))

theorem minor_mul {r : ℕ} (u B : Matrix (Fin r) (Fin r) Ω₃) (hB : ∀ m' m : Fin r, (m : ℕ) + 1 ≤ m' → B m' m = 0) (m : Fin r)
    (I : Fin (m + 1) → Fin r) :
    (Matrix.of fun a b : Fin (m + 1) => (u * B) (I a) (Fin.castLE m.2 b)).det =
      (∏ m' ∈ Finset.Iic m, B m' m') * (Matrix.of fun a b : Fin (m + 1) => u (I a) (Fin.castLE m.2 b)).det := by
  have e : (Matrix.of fun a b : Fin (m + 1) => (u * B) (I a) (Fin.castLE m.2 b)) =
      (Matrix.of fun a b : Fin (m + 1) => u (I a) (Fin.castLE m.2 b)) *
        Matrix.of fun a b : Fin (m + 1) => B (Fin.castLE m.2 a) (Fin.castLE m.2 b) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    symm
    refine Finset.sum_of_injOn (Fin.castLE m.2) (fun _ _ _ _ h => Fin.castLE_injective _ h) (by simp) (fun l _ hl => ?_)
      fun _ _ => rfl
    rw [hB, mul_zero]
    by_contra h
    refine hl ⟨⟨l, ?_⟩, by simp, rfl⟩
    have := b.2
    simp only [Fin.val_castLE] at h
    omega
  rw [e, Matrix.det_mul, mul_comm, Matrix.det_of_isUpperTriangular, ← prod_castLE m fun m' => B m' m']
  · rfl
  · intro a b h
    exact hB _ _ h

end

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushJoin
section
noncomputable section

namespace SheetDecomposition

open scoped TensorProduct

namespace Join

theorem tower {P Ω : Type} [Field P] [Field Ω] (φ : P →+* Ω) (K₀ : Subfield P) :
    Module.finrank (K₀.map φ) Ω = Module.finrank K₀ P * Module.finrank φ.fieldRange Ω := by
  letI : Algebra P Ω := φ.toAlgebra
  letI : Algebra K₀ Ω := (φ.comp K₀.subtype).toAlgebra
  haveI : IsScalarTower K₀ P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Module.finrank P Ω = Module.finrank φ.fieldRange Ω :=
    Algebra.finrank_eq_of_equiv_equiv φ.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)
  have h2 : Module.finrank K₀ Ω = Module.finrank (K₀.map φ) Ω :=
    Algebra.finrank_eq_of_equiv_equiv (K₀.toSubring.equivMapOfInjective φ φ.injective) (RingEquiv.refl Ω)
      (RingHom.ext fun _ => rfl)
  rw [← h1, ← h2, Module.finrank_mul_finrank]

theorem finrank_congr {Ω : Type} [Field Ω] {A B : Subfield Ω} (h : A = B) : Module.finrank A Ω = Module.finrank B Ω := by
  subst h; rfl

theorem map_adjoin {F P Ω : Type} [Field F] [Field P] [Field Ω] [Algebra F P] [Algebra F Ω] (φ : P →+* Ω)
    (hφ : φ.comp (algebraMap F P) = algebraMap F Ω) {I : Type} (w : I → P) :
    (IntermediateField.adjoin F (Set.range w)).toSubfield.map φ =
      (IntermediateField.adjoin F (Set.range fun q => φ (w q))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, ← hφ]
  rfl

theorem core (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B] {I : Type} (w : I → B) (d₂ e : ℕ)
    (hw : AlgebraicIndependent F w) (hd : 0 < d₂) (hB : Module.finrank (IntermediateField.adjoin F (Set.range w)) B = d₂)
    (he : 0 < e) (hA : Module.finrank F A = e) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra A Ω) (i : B →+* Ω) (d n : ℕ),
      i.comp (algebraMap F B) = (algebraMap A Ω).comp (algebraMap F A) ∧ AlgebraicIndependent A (fun q => i (w q)) ∧ 0 < d ∧
      Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω = d ∧
      Module.finrank i.fieldRange Ω = n ∧ 0 < n ∧ n * d₂ = d * e := by
  haveI : FiniteDimensional F A := Module.finite_of_finrank_pos (hA ▸ he)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (B ⊗[F] A)
  letI : Field ((B ⊗[F] A) ⧸ m) := Ideal.Quotient.field m
  let j : A →ₐ[F] ((B ⊗[F] A) ⧸ m) := (Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight
  letI : Algebra A ((B ⊗[F] A) ⧸ m) := j.toRingHom.toAlgebra
  haveI : IsScalarTower F A ((B ⊗[F] A) ⧸ m) := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Module.Finite B ((B ⊗[F] A) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ B m).toLinearMap (Ideal.Quotient.mkₐ_surjective B m)
  let Ω := ((B ⊗[F] A) ⧸ m)
  let i : B →+* Ω := algebraMap B Ω
  have hi : i.comp (algebraMap F B) = algebraMap F Ω := (IsScalarTower.algebraMap_eq F B Ω).symm
  have hx0 : AlgebraicIndependent F (fun q => i (w q)) :=
    hw.map' (f := IsScalarTower.toAlgHom F B Ω) (algebraMap B Ω).injective
  have hx : AlgebraicIndependent A (fun q => i (w q)) := hx0.extendScalars A
  have hn : 0 < Module.finrank i.fieldRange Ω := by
    rw [← Algebra.finrank_eq_of_equiv_equiv i.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)]
    exact Module.finrank_pos
  have t1 := tower i (IntermediateField.adjoin F (Set.range w)).toSubfield
  rw [finrank_congr (map_adjoin i hi w)] at t1
  let P := FractionRing (MvPolynomial I A)
  let φ : P →+* Ω := (IntermediateField.adjoin A (Set.range fun q => i (w q))).val.toRingHom.comp hx.aevalEquivField.toRingEquiv.toRingHom
  letI : Algebra F P := ((algebraMap A P).comp (algebraMap F A)).toAlgebra
  have hφA : ∀ a, φ (algebraMap A P a) = algebraMap A Ω a := fun a => congrArg Subtype.val (hx.aevalEquivField.commutes a)
  have hφ : φ.comp (algebraMap F P) = algebraMap F Ω := RingHom.ext fun a =>
    (hφA _).trans (IsScalarTower.algebraMap_apply F A Ω a).symm
  have hX : (fun q => φ (algebraMap (MvPolynomial I A) P (MvPolynomial.X q))) = fun q => i (w q) := funext fun q =>
    (hx.aevalEquivField_algebraMap_apply_coe _).trans (MvPolynomial.aeval_X _ q)
  have hr : φ.fieldRange = (IntermediateField.adjoin A (Set.range fun q => i (w q))).toSubfield := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hx.aevalEquivField y).2
    · intro hz
      exact ⟨hx.aevalEquivField.symm ⟨z, hz⟩, congrArg Subtype.val (hx.aevalEquivField.apply_symm_apply ⟨z, hz⟩)⟩
  have t2 := tower φ (IntermediateField.adjoin F (Set.range fun q => algebraMap (MvPolynomial I A) P (MvPolynomial.X q))).toSubfield
  rw [finrank_congr (map_adjoin φ hφ _), hX, finrank_congr hr] at t2
  have t3 := GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq F A I rfl
  have key : d₂ * Module.finrank i.fieldRange Ω =
      e * Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω := by
    rw [← hB, ← hA, ← t3]
    exact t1.symm.trans t2
  refine ⟨Ω, inferInstance, inferInstance, i, _, _, hi.trans (IsScalarTower.algebraMap_eq F A Ω), hx, ?_, rfl, rfl, hn, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, mul_zero] at key
    exact (Nat.mul_pos hd hn).ne' key
  · rw [mul_comm, key, mul_comm]

theorem adjoin_entries (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1) (h0 : ∀ s l m, l < m → u s l m = 0) :
    IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k
        (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    show u s l m ∈ _
    rcases lt_trichotomy l m with h | rfl | h
    · rw [h0 s l m h]; exact zero_mem _
    · rw [h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, m), h⟩⟩, rfl⟩
  · rintro _ ⟨⟨s, lm, h⟩, rfl⟩
    exact ⟨⟨s, lm⟩, rfl⟩

end Join

theorem fieldJoin : FieldJoin := by
  intro Ω₀ Ω₁ Ω₂ _ _ _ _ _ S _ r u d₂ e ⟨h1, h0, hi, hd, hf⟩ he hA
  rw [Join.adjoin_entries Ω₀ u h1 h0] at hf
  obtain ⟨Ω, _, _, i, d, n, a1, a2, a3, a4, a5, a6, a7⟩ := Join.core Ω₀ Ω₁ Ω₂ _ d₂ e hi hd hf he hA
  have g1 : ∀ s m, (u s).map i m m = 1 := fun s m => by simp [h1]
  have g0 : ∀ s l m, l < m → (u s).map i l m = 0 := fun s l m h => by simp [h0 s l m h]
  refine ⟨Ω, inferInstance, inferInstance, i, d, n, a1, ⟨g1, g0, a2, a3, ?_⟩, a5, a6, a7⟩
  rw [Join.adjoin_entries Ω₁ (fun s => (u s).map i) g1 g0]
  exact a4

end SheetDecomposition
end
end

