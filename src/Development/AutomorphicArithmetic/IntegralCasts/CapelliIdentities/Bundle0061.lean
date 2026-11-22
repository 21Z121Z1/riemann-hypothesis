import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanTopFamily
section
noncomputable def UpperTheory.Reformulated.B.SpanTopFamily.Mι :
    {E K : Type} →
      [inst : Field E] →
        [inst_1 : Field K] →
          (O : ValuationSubring K) →
            (E →+* K) → {n : Type} → Submodule (NumberField.RingOfIntegers E) (n → E) → Submodule (↥O) (n → K) :=
    fun {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
        (L : Submodule (NumberField.RingOfIntegers E) (n → E)) ↦
      Submodule.span (↥O) ((fun (l : n → E) (j : n) ↦ (ι : E → K) (l j)) '' (↑L : Set (n → E)))

theorem UpperTheory.Reformulated.B.SpanTopFamily.span_top :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by
  intro E K _ _ _ O ι n _ _ L hL
  have key : ∀ v : n → E, v ∈ Submodule.span E (↑L : Set (n → E)) →
      (fun j => ι (v j)) ∈ Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero =>
      have : (fun j : n => ι ((0 : n → E) j)) = 0 := by
        funext j; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun j : n => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
        funext j; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun j : n => ι ((a • x) j)) = ι a • (fun j => ι (x j)) := by
        funext j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ' w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := key (Pi.single i 1) (by rw [hL]; trivial)
  have e : (fun j : n => ι ((Pi.single i 1 : n → E) j)) = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialMapFinite
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R' ⟶ UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

theorem UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main :
    ∀ {A : Type} [inst : CommRing A] {Y Z : AlgebraicGeometry.Scheme} {f g : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp A ⟶ Y} (s : Y ⟶ Z)
      [AlgebraicGeometry.IsSeparated s],
      CategoryTheory.CategoryStruct.comp f s = CategoryTheory.CategoryStruct.comp g s →
        ∀ {N : Type} (I : N → Ideal A),
          (∀ (x : A), (∀ (n : N), x ∈ I n) → x = (0 : A)) →
            (∀ (n : N),
                CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) f =
                  CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) g) →
              f = g := by
  open AlgebraicGeometry CategoryTheory CategoryTheory.Limits in
  intro A _ Y Z f g s _ h N I hI hn
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  have : IsSeparated Y'.hom := ‹_›
  have : IsAffine X'.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hcl : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  obtain ⟨haff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (equalizer.ι f' g').left
  have hfac : ∀ n, ∃ l : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp (A ⧸ I n) ⟶ (equalizer f' g').left,
      l ≫ (equalizer.ι f' g').left = UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) := by
    intro n
    let T' : Over Z := Over.mk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) ≫ f ≫ s)
    let ι' : T' ⟶ X' := Over.homMk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)))
    have hc : ι' ≫ f' = ι' ≫ g' := by
      ext1
      exact hn n
    refine ⟨(equalizer.lift ι' hc).left, ?_⟩
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hinj : Function.Injective (equalizer.ι f' g').left.appTop := by
    refine (injective_iff_map_eq_zero (equalizer.ι f' g').left.appTop.hom).mpr fun y hy ↦ ?_
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = y :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom y, by simp⟩
    have ha : a = 0 := by
      refine hI a fun n ↦ ?_
      obtain ⟨l, hl⟩ := hfac n
      have h1 : (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 0 := by
        rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [hy]
        exact map_zero _
      have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))
      have h3 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).inv (Ideal.Quotient.mk (I n) a) = 0 := by
        have h4 := congr($h2 a)
        simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h4
        exact h4.trans h1
      have h5 := congr((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).hom $h3)
      simp only [map_zero] at h5
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using h5
    simp [ha]
  have hiso : IsIso (equalizer.ι f' g').left.appTop := by
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  have hE : IsIso (equalizer.ι f' g').left :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (equalizer.ι f' g').left)).mpr
      (inferInstanceAs (IsIso (Spec.map (equalizer.ι f' g').left.appTop)))
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpectrumNonemptyOfCountableRank
section
open Polynomial in
private lemma spectrum_nonempty_of_countable_rank {V : Type} [AddCommGroup V] [_root_.Module ℂ V]
    [Nontrivial V] (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (T : Module.End ℂ V) :
    (spectrum ℂ T).Nonempty := by
  classical
  by_contra hne
  have hunit : ∀ a : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) a) := fun a => by
    have h : a ∉ spectrum ℂ T := fun h => hne ⟨a, h⟩
    rw [spectrum.notMem_iff] at h
    exact IsUnit.sub_iff.mp h
  have hR : ∀ a : ℂ, ∃ R : Module.End ℂ V, (T - algebraMap ℂ (Module.End ℂ V) a) * R = 1 :=
    fun a => (hunit a).exists_right_inv
  choose R hR using hR
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hdep : ¬ LinearIndependent ℂ (fun a : ℂ => R a v) := by
    intro hli
    have h1 := hli.cardinal_le_rank
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)
  rw [linearIndependent_iff'] at hdep
  push_neg at hdep
  obtain ⟨s, m, hm, i, hi, hmi⟩ := hdep
  let q : ℂ → ℂ[X] := fun a => ∏ j ∈ s.erase a, (X - C j)
  let p : ℂ[X] := ∑ a ∈ s, C (m a) * q a
  have key : ∀ a ∈ s, aeval T (∏ j ∈ s, (X - C j)) * R a = aeval T (q a) := by
    intro a ha
    rw [← Finset.prod_erase_mul s _ ha, map_mul, mul_assoc]
    have : aeval T (X - C a) = T - algebraMap ℂ (Module.End ℂ V) a := by simp
    rw [this, hR, mul_one]
  have hp : aeval T p v = 0 := by
    have h1 := congrArg (aeval T (∏ j ∈ s, (X - C j))) hm
    rw [map_zero, map_sum] at h1
    rw [← h1]
    simp only [p, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, aeval_C, ← key a ha, map_smul]
    simp [Module.End.mul_apply, Module.algebraMap_end_apply]
  have hp0 : p ≠ 0 := by
    intro h0
    have h1 : eval i p = m i * ∏ j ∈ s.erase i, (i - j) := by
      simp only [p, eval_finset_sum, eval_mul, eval_C]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [q, eval_prod]
      · intro b hb hbi
        have : eval i (q b) = 0 := by
          simp only [q, eval_prod]
          refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hbi.symm, hi⟩) (by simp)
        rw [this, mul_zero]
    rw [h0, eval_zero] at h1
    have h2 : ∏ j ∈ s.erase i, (i - j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    exact (mul_ne_zero hmi h2) h1.symm
  have hnu : ¬ IsUnit (aeval T p) := by
    intro hu
    have hinj := ((Module.End.isUnit_iff _).mp hu).injective
    exact hv (hinj (by rw [hp, map_zero]))
  have hprod := (IsAlgClosed.splits p).eq_prod_roots
  have lead_ne := leadingCoeff_ne_zero.mpr hp0
  have lead_unit : IsUnit (algebraMap ℂ (Module.End ℂ V) p.leadingCoeff) :=
    (Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  rw [hprod, aeval_mul, ((Commute.all _ _).map (aeval T : ℂ[X] →ₐ[ℂ] _)).isUnit_mul_iff,
    aeval_C] at hnu
  obtain ⟨k, hk, -⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod (not_and.mp hnu lead_unit)
  exact hne ⟨k, hk⟩

theorem UpperTheory.Reformulated.B.DYhd6.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [Nontrivial V],
      Module.rank ℂ V ≤ Cardinal.aleph0 →
        ∀ (B : Subalgebra ℂ (Module.End ℂ V)),
          (∀ (N : Submodule ℂ V), (∀ b ∈ B, ∀ x ∈ N, (b : V → V) x ∈ N) → N = ⊥ ∨ N = ⊤) →
            ∀ (f : Module.End ℂ V) (s : Finset V), ∃ b ∈ B, ∀ m ∈ s, (f : V → V) m = (b : V → V) m := by
  intro V _ _ _ hV B hB f s
  have hsc : ∀ (c : ℂ) (x : V), c • x = (algebraMap ℂ B c) • x := fun c x => by
    change c • x = ((algebraMap ℂ (Module.End ℂ V) c : Module.End ℂ V)) x
    simp [Module.algebraMap_end_apply]
  have hbc : ∀ (b : B) (c : ℂ) (x : V), b • (c • x) = c • (b • x) := fun b c x =>
    (b : Module.End ℂ V).map_smul c x
  haveI hsimple : IsSimpleModule B V :=
    { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
      eq_bot_or_eq_top := fun N => by
        let N' : Submodule ℂ V :=
          { carrier := N
            add_mem' := fun h1 h2 => N.add_mem h1 h2
            zero_mem' := N.zero_mem
            smul_mem' := fun c x hx => by
              rw [hsc]
              exact N.smul_mem _ hx }
        rcases hB N' (fun b hb x hx => N.smul_mem (⟨b, hb⟩ : B) hx) with h | h
        · left
          rw [eq_bot_iff]
          intro x hx
          have : x ∈ N' := hx
          rw [h] at this
          simpa using this
        · right
          rw [eq_top_iff]
          intro x _
          have : x ∈ N' := by rw [h]; trivial
          exact this }
  have hscal : ∀ d : Module.End B V, ∃ a : ℂ, ∀ x, d x = a • x := by
    intro d
    let T : Module.End ℂ V :=
      { toFun := d
        map_add' := d.map_add
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          rw [hsc, d.map_smul, ← hsc] }
    obtain ⟨a, ha⟩ := spectrum_nonempty_of_countable_rank hV T
    let e : V →ₗ[B] V :=
      { toFun := fun x => a • x - d x
        map_add' := fun x y => by
          rw [smul_add, d.map_add]
          abel
        map_smul' := fun b x => by
          simp only [RingHom.id_apply]
          rw [d.map_smul, smul_sub, hbc] }
    rcases LinearMap.bijective_or_eq_zero e with hb | h0
    · exfalso
      apply ha
      rw [spectrum.mem_resolventSet_iff, Module.End.isUnit_iff]
      have hfe : ⇑(algebraMap ℂ (Module.End ℂ V) a - T) = ⇑e := by
        funext x
        simp [T, e, Module.algebraMap_end_apply]
      rw [hfe]
      exact hb
    · refine ⟨a, fun x => ?_⟩
      have : a • x - d x = 0 := congrArg (fun g : V →ₗ[B] V => g x) h0
      exact (sub_eq_zero.mp this).symm
  let F : Module.End (Module.End B V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun d x => by
        obtain ⟨a, ha⟩ := hscal d
        simp only [RingHom.id_apply, Module.End.smul_def]
        rw [ha, ha, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun m hm => hr m hm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SplittingFieldConstruction
section
open Polynomial

noncomputable def UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField :
    Prop :=
    ∀ (A B : Type) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : CommRing B] [inst_3 : Algebra A B]
      [Module.Finite A B],
      ∃ (L : Type) (x : Field L) (x_1 : Algebra A L) (x_2 : Algebra (FractionRing A) L) (_ :
        IsScalarTower A (FractionRing A) L),
        FiniteDimensional (FractionRing A) L ∧
          Normal (FractionRing A) L ∧
            Finite (B →ₐ[A] ↥(integralClosure A L)) ∧
              ∀ (Ω : Type) [inst_5 : Field Ω] (φ : ↥(integralClosure A L) →+* Ω) (z : B →+* Ω),
                Function.Injective (⇑(φ.comp (Algebra.algebraMap A ↥(integralClosure A L))) : A → Ω) →
                  z.comp (Algebra.algebraMap A B) = φ.comp (Algebra.algebraMap A ↥(integralClosure A L)) →
                    ∃! σ : B →ₐ[A] ↥(integralClosure A L), φ.comp (↑σ : B →+* ↥(integralClosure A L)) = z

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (s : Finset B) :
    ∃ p : A[X], p.Monic ∧ ∀ b ∈ s, aeval b p = 0 := by
  have h : ∀ b : B, ∃ q : A[X], q.Monic ∧ aeval b q = 0 := fun b =>
    (Algebra.IsIntegral.isIntegral (R := A) b)
  choose q hq hq0 using h
  refine ⟨∏ b ∈ s, q b, monic_prod_of_monic _ _ fun b _ => hq b, fun b hb => ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero hb (hq0 b)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom {A B C : Type} [CommRing A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] (s : Finset B)
    (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) : Finite (B →ₐ[A] C) := by
  let f : (B →ₐ[A] C) → (s → p.rootSet C) := fun σ b =>
    ⟨σ b, by
      rw [hp.mem_rootSet, aeval_algHom_apply, h0 b b.2, map_zero]⟩
  refine Finite.of_injective f fun σ τ h => ?_
  apply AlgHom.toLinearMap_injective
  refine LinearMap.ext_on hs fun b hb => ?_
  exact congrArg Subtype.val (congrFun h ⟨b, hb⟩)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.factor {A B C Ω : Type} [CommRing A] [Nontrivial A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra.IsIntegral A C] [Field Ω]
    (s : Finset B) (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) (hsp : (p.map (algebraMap A C)).Splits)
    (φ : C →+* Ω) (z : B →+* Ω) (hinj : Function.Injective (φ.comp (algebraMap A C)))
    (hz : z.comp (algebraMap A B) = φ.comp (algebraMap A C)) :
    ∃! σ : B →ₐ[A] C, φ.comp (σ : B →+* C) = z := by
  have hφ : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hzA : ∀ a : A, z (algebraMap A B a) = φ (algebraMap A C a) := fun a =>
    DFunLike.congr_fun hz a
  have hgen : ∀ b ∈ s, z b ∈ φ.range := by
    intro b hb
    have h1 : eval (z b) ((p.map (algebraMap A C)).map φ) = 0 := by
      rw [Polynomial.map_map, ← hz, eval_map, ← hom_eval₂, ← aeval_def, h0 b hb, map_zero]
    rw [hsp.eq_prod_roots_of_monic (hp.map _), Polynomial.map_multiset_prod,
      eval_multiset_prod, Multiset.prod_eq_zero_iff] at h1
    simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply, Polynomial.map_sub,
      map_X, map_C, eval_sub, eval_X, eval_C] at h1
    obtain ⟨c, -, hc⟩ := h1
    exact ⟨c, (sub_eq_zero.1 hc).symm⟩
  have hall : ∀ b : B, z b ∈ φ.range := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hzA]
      exact mul_mem ⟨_, rfl⟩ hx
  choose g hg using hall
  let σ : B →ₐ[A] C :=
    { toFun := g
      map_one' := hφ (by rw [hg, map_one, map_one])
      map_mul' := fun x y => hφ (by rw [map_mul φ, hg, hg, hg, map_mul])
      map_zero' := hφ (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => hφ (by rw [map_add φ, hg, hg, hg, map_add])
      commutes' := fun a => hφ (by rw [hg, hzA]) }
  refine ⟨σ, RingHom.ext fun b => hg b, fun τ hτ => AlgHom.ext fun b => hφ ?_⟩
  exact (DFunLike.congr_fun hτ b).trans (hg b).symm

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure {A L : Type} [CommRing A] [Field L]
    [Algebra A L] (p : A[X]) (hp : p.Monic) (hsp : (p.map (algebraMap A L)).Splits) :
    (p.map (algebraMap A (integralClosure A L))).Splits := by
  have hm : (p.map (algebraMap A (integralClosure A L))).map
      (algebraMap (integralClosure A L) L) = p.map (algebraMap A L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  refine Splits.of_splits_map_of_injective (i := algebraMap (integralClosure A L) L)
    Subtype.val_injective (hm ▸ hsp) fun a ha => ?_
  rw [hm] at ha
  have h1 := isRoot_of_mem_roots ha
  rw [IsRoot.def, eval_map] at h1
  exact ⟨⟨a, p, hp, h1⟩, rfl⟩

theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of :
    UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField := by
  intro A B _ _ _ _ _
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  obtain ⟨p, hp, h0⟩ := UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic (A := A) s
  let q : (FractionRing A)[X] := p.map (algebraMap A (FractionRing A))
  let L : Type := q.SplittingField
  letI iK : Algebra (FractionRing A) L := inferInstance
  letI iA : Algebra A L :=
    ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI iT : @IsScalarTower A (FractionRing A) L Algebra.toSMul iK.toSMul iA.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hsp : (p.map (algebraMap A L)).Splits := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L, ← Polynomial.map_map]
    exact SplittingField.splits q
  refine ⟨L, inferInstance, iA, iK, iT, inferInstance, inferInstance,
    UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom s hs p hp h0, ?_⟩
  intro Ω _ φ z hinj hz
  exact UpperTheory.Reformulated.B.SplittingFieldConstruction.factor s hs p hp h0
    (UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure p hp hsp) φ z hinj hz
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SqShift
section
theorem UpperTheory.Reformulated.B.Qk59.sq_shift :
    ∀ {G : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    {μ : MeasureTheory.Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) D μ →
      ∀ {f : G → ℝ},
        (∀ γ ∈ Γ, ∀ (y : G), f (γ * y) = f y) → ∀ (g : G), ∫ (y : G) in D, f (y * g) ∂μ = ∫ (y : G) in D, f y ∂μ := by
  intro G _ _ _ _ _ μ _ _ Γ _ D hD f hf g
  have hD' : MeasureTheory.IsFundamentalDomain (↥Γ) ((fun y : G => y * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv
      (MeasureTheory.measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id
      (fun γ y => by
        show ((γ : G) * y) * g⁻¹ = (γ : G) * (y * g⁻¹)
        exact mul_assoc _ _ _)
  have h1 := (MeasureTheory.measurePreserving_mul_right μ g).setIntegral_preimage_emb
    (measurableEmbedding_mulRight g) f ((fun y : G => y * g⁻¹) ⁻¹' D)
  have h2 : (fun y : G => y * g) ⁻¹' ((fun y : G => y * g⁻¹) ⁻¹' D) = D := by
    ext y
    simp
  rw [h2] at h1
  rw [h1]
  exact hD'.setIntegral_eq hD (fun γ y => hf γ γ.2 y)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Stabilizer
section
noncomputable def UpperTheory.Reformulated.B.RepresentationVectorStabilizer.stab :
    {Γ X : Type} →
      [inst : Group Γ] → [inst_1 : AddCommGroup X] → [inst_2 : _root_.Module ℂ X] → Representation ℂ Γ X → X → Subgroup Γ :=
  fun {Γ _} _ _ _ ρ x =>
    { carrier := {g : Γ | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one, Module.End.one_apply]
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by rw [inv_mul_cancel, map_one, Module.End.one_apply] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerIsOpen
section
theorem UpperTheory.Reformulated.B.StabilizerIsOpen.stab_open.{u_1, u_2} :
    ∀ {G : Type u_1} {V : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : AddCommGroup V] [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
    {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} ∈ nhds (1 : G) →
      IsOpen {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {k : G | ρ k v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h1 }
  exact H.isOpen_of_mem_nhds h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerOf
section
noncomputable def UpperTheory.Reformulated.B.StabilizerOf.stabilizerOf.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] →
        {V : Type u_2} → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G} _ {_V} _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      one_mem' := by
        show ρ 1 v = v
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by rw [inv_mul_cancel, map_one]; rfl }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumChar
section
theorem UpperTheory.Reformulated.B.Qe46.sum_char :
    ∀ {G : Type} [inst : CommGroup G] [inst_1 : Fintype G] (χ : G →* ℂˣ),
    χ ≠ (1 : G →* ℂˣ) → ∑ z : G, (↑((χ : G → ℂˣ) z) : ℂ) = (0 : ℂ) := by
  intro G _ _ χ hχ
  have hne : (Units.coeHom ℂ).comp χ ≠ 1 := by
    intro h
    apply hχ
    ext z
    have hz := DFunLike.congr_fun h z
    simpa using hz
  simpa using sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) hne
end

