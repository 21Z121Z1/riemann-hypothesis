import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexAtSinglePlace
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex

variable {L : Type} [Field L] [NumberField L] {W : Type} [AddCommGroup W] [Module (𝓞 L) W]

def cond (A B : Submodule (𝓞 L) W) : Ideal (𝓞 L) where
  carrier := {u | ∀ x ∈ A, u • x ∈ B}
  add_mem' := fun {a b} ha hb x hx => by
    rw [add_smul]; exact B.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by rw [zero_smul]; exact B.zero_mem
  smul_mem' := fun c u hu x hx => by
    rw [smul_eq_mul, mul_smul]; exact B.smul_mem c (hu x hx)

theorem mem_cond {A B : Submodule (𝓞 L) W} {u : 𝓞 L} :
    u ∈ cond A B ↔ ∀ x ∈ A, u • x ∈ B := Iff.rfl

theorem exists_reps {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ S : Finset W, (∀ r ∈ S, r ∈ A) ∧ ∀ x ∈ A, ∃ r ∈ S, x - r ∈ B := by
  classical
  have hQ : Finite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hfin
  have := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  refine ⟨Finset.univ.image
    (fun q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup =>
      ((Quotient.out q : A.toAddSubgroup) : W)), ?_, ?_⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact (Quotient.out q).2
  · intro x hx
    let q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup :=
      QuotientAddGroup.mk ⟨x, hx⟩
    refine ⟨((Quotient.out q : A.toAddSubgroup) : W),
      Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    have hq : (QuotientAddGroup.mk (Quotient.out q) :
        A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) = q := Quotient.out_eq q
    have h := QuotientAddGroup.eq.mp hq
    rw [AddSubgroup.mem_addSubgroupOf] at h
    have h' : -((Quotient.out q : A.toAddSubgroup) : W) + x ∈ B := h
    rwa [neg_add_eq_sub] at h'

theorem cond_ne_bot {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) : cond A B ≠ ⊥ := by
  intro hbot

  have hmem : ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : 𝓞 L) ∈ cond A B := by
    refine mem_cond.mpr fun x hx => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup hx
  rw [hbot, Ideal.mem_bot] at hmem
  exact hfin (Nat.cast_eq_zero.mp hmem)

theorem exists_mem_cond_notMem {A B : Submodule (𝓞 L) W} (w : FinitePlace L)
    (hloc : locAt w A = locAt w B)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ s ∈ cond A B, s ∉ w.maximalIdeal.asIdeal := by
  classical
  obtain ⟨S, hSA, hS⟩ := exists_reps hfin
  have hex : ∀ r ∈ S, ∃ t : 𝓞 L, t ∉ w.maximalIdeal.asIdeal ∧ t • r ∈ B := by
    intro r hr
    have hr' : r ∈ locAt w B := by rw [← hloc]; exact le_locAt w A (hSA r hr)
    exact mem_locAt.mp hr'
  choose! t ht using hex
  have := w.maximalIdeal.isPrime
  refine ⟨∏ r ∈ S, t r, mem_cond.mpr fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, hxr⟩ := hS x hx
    have hrB : (∏ r ∈ S, t r) • r ∈ B := by
      rw [← Finset.mul_prod_erase S t hr, mul_comm, mul_smul]
      exact B.smul_mem _ (ht r hr).2
    have hx' : x = r + (x - r) := by abel
    rw [hx', smul_add]
    exact B.add_mem hrB (B.smul_mem _ hxr)
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨r, hr, hmem⟩
    exact (ht r hr).1 hmem

theorem cond_sup_span_eq_top {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) : cond A B ⊔ Ideal.span {t} = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hPbot : P ≠ ⊥ := by
    intro hP
    apply cond_ne_bot hfin
    rw [eq_bot_iff, ← hP]
    exact le_sup_left.trans hle
  obtain ⟨Q, hQ⟩ : ∃ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal = P :=
    ⟨⟨P, hPmax.isPrime, hPbot⟩, rfl⟩
  by_cases hw : FinitePlace.mk Q = v
  · apply ht
    rw [← hw, FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  · obtain ⟨s, hs, hsP⟩ := exists_mem_cond_notMem (FinitePlace.mk Q) (hloc _ hw) hfin
    apply hsP
    rw [FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_left hs)

theorem exists_bezout {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) :
    ∃ s u : 𝓞 L, u ∈ cond A B ∧ s * t + u = 1 := by
  have h1 : (1 : 𝓞 L) ∈ cond A B ⊔ Ideal.span {t} := by
    rw [cond_sup_span_eq_top v hfin hloc ht]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨s, u, hu, by rw [add_comm]; exact huz⟩

theorem relIndex_locAt (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W]
    [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W) (hBA : B ≤ A)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) :
    (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup =
      B.toAddSubgroup.relIndex A.toAddSubgroup := by
  have hle : A.toAddSubgroup ≤ (locAt v A).toAddSubgroup := fun x hx => le_locAt v A hx

  have hback : ∀ x ∈ A, x ∈ locAt v B → x ∈ B := by
    intro x hxA hx
    obtain ⟨t, ht, htx⟩ := mem_locAt.mp hx
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    have hx' : x = s • (t • x) + u • x := by rw [smul_smul, ← add_smul, hsu, one_smul]
    rw [hx']
    exact B.add_mem (B.smul_mem s htx) (mem_cond.mp hu x hxA)

  let f := (QuotientAddGroup.mk' ((locAt v B).toAddSubgroup.addSubgroupOf
    (locAt v A).toAddSubgroup)).comp (AddSubgroup.inclusion hle)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    obtain ⟨t, ht, hty⟩ := mem_locAt.mp hy
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    refine ⟨⟨s • (t • y), A.smul_mem s hty⟩, ?_⟩
    simp only [f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(s • (t • y)) + y ∈ locAt v B
    have hu' : u = 1 - s * t := by rw [← hsu]; ring
    have hyeq : -(s • (t • y)) + y = u • y := by
      rw [hu', sub_smul, one_smul, smul_smul, neg_add_eq_sub]
    rw [hyeq]
    exact mem_locAt.mpr ⟨t, ht, by rw [smul_comm]; exact mem_cond.mp hu _ hty⟩
  have hker : f.ker = B.toAddSubgroup.addSubgroupOf A.toAddSubgroup := by
    ext ⟨x, hx⟩
    simp only [f, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion,
      Submodule.mem_toAddSubgroup]
    exact ⟨fun h => hback x hx h, fun h => le_locAt v B h⟩
  unfold AddSubgroup.relIndex
  rw [← hker, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModule
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Basis

theorem projective_of_torsionFree {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M] : Module.Projective R M := by
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  exact Module.Flat.projective_of_finitePresentation

theorem finrank_ideal {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊥) :
    Module.finrank R I = 1 := by
  have h := Submodule.finrank_quotient_add_finrank I
  have h0 : Module.finrank R (R ⧸ I) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    intro x
    refine ⟨a, ha0, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right y ha
  rw [h0, zero_add, Module.finrank_self] at h
  exact h

theorem exists_ideal_cover {R : Type} [CommRing R] [IsDedekindDomain R] (g : ℕ) :
    ∀ (B : Type) [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.IsTorsionFree R B],
      Module.finrank R B = g →
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal R) (b : ∀ i, I i →ₗ[R] B),
        Fintype.card ι = g ∧ (∀ i, I i ≠ ⊥) ∧ ⨆ i, LinearMap.range (b i) = ⊤ := by
  induction g with
  | zero =>
    intro B _ _ _ _ hB
    have hs : Subsingleton B := by
      refine subsingleton_of_forall_eq 0 fun x => ?_
      obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 hB x
      exact (smul_eq_zero.1 hax).resolve_left ha
    refine ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, by simp, fun i => i.elim, ?_⟩
    exact Subsingleton.elim _ _
  | succ g ih =>
    intro B _ _ _ _ hB
    haveI : Module.Projective R B := projective_of_torsionFree
    haveI : Nontrivial B := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      rw [Module.finrank_zero_of_subsingleton] at hB
      omega
    obtain ⟨x, hx⟩ := exists_ne (0 : B)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hx
    let J : Ideal R := LinearMap.range f
    have hJ : J ≠ ⊥ := fun h => hf (by
      have : f x ∈ J := ⟨x, rfl⟩
      rw [h] at this
      simpa using this)
    haveI : Module.Projective R J := projective_of_torsionFree
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
      (LinearMap.range_rangeRestrict f)
    have hrank : Module.finrank R (LinearMap.ker f) = g := by
      have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
      rw [f.quotKerEquivRange.finrank_eq, hB] at h1
      have h2 : Module.finrank R (LinearMap.range f) = 1 := finrank_ideal J hJ
      omega
    obtain ⟨ι, _, I, b, hc, hI, hsup⟩ := ih (LinearMap.ker f) hrank
    let I' : Option ι → Ideal R := fun o => o.elim J I
    let b' : ∀ o, I' o →ₗ[R] B := fun o => match o with
      | none => s
      | some i => (LinearMap.ker f).subtype ∘ₗ b i
    refine ⟨Option ι, inferInstance, I', b', by simp [hc], ?_, ?_⟩
    · rintro (_ | i)
      · exact hJ
      · exact hI i
    · set T : Submodule R B := ⨆ o, LinearMap.range (b' o) with hT
      have hker : (⨆ i, LinearMap.range (b i)) ≤ T.comap (LinearMap.ker f).subtype := by
        refine iSup_le fun i => ?_
        rintro _ ⟨a, rfl⟩
        exact Submodule.mem_iSup_of_mem (some i) ⟨a, rfl⟩
      rw [hsup] at hker
      rw [eq_top_iff]
      intro z _
      have hz : f (z - s (f.rangeRestrict z)) = 0 := by
        have h3 : f.rangeRestrict (s (f.rangeRestrict z)) = f.rangeRestrict z :=
          LinearMap.congr_fun hs _
        have h4 : f (s (f.rangeRestrict z)) = f z := congrArg Subtype.val h3
        rw [map_sub, h4, sub_self]
      have h5 : z - s (f.rangeRestrict z) ∈ T :=
        hker (Submodule.mem_top (x := (⟨_, hz⟩ : LinearMap.ker f)))
      have h6 : s (f.rangeRestrict z) ∈ T :=
        Submodule.mem_iSup_of_mem none ⟨f.rangeRestrict z, rfl⟩
      simpa using T.add_mem h5 h6

theorem span_of_root (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (h : ℕ) (hh : h ≠ 0) (c : 𝓞 K)
    (hc : I ^ h = Ideal.span {c}) (z : K') (hz : z ^ h = algebraMap K K' (c : K)) :
    ∃ y : 𝓞 K', y ≠ 0 ∧ I.map (algebraMap (𝓞 K) (𝓞 K')) = Ideal.span {y} := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hc
    exact pow_ne_zero h hI hc
  have hcK : (c : K) ≠ 0 := fun h0 => hc0 (RingOfIntegers.ext h0)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hh] at hz
    exact hcK ((map_eq_zero _).mp hz.symm)
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hh) ?_
    rw [hz]
    exact (c.2 : IsIntegral ℤ (c : K)).map (IsScalarTower.toAlgHom ℤ K K')
  let y : 𝓞 K' := ⟨z, hint⟩
  have hyz : (y : K') = z := rfl
  have hy0 : y ≠ 0 := fun h0 => hz0 (by rw [← hyz, h0]; rfl)
  have hyc : y ^ h = algebraMap (𝓞 K) (𝓞 K') c := by
    apply RingOfIntegers.ext
    exact (map_pow (algebraMap (𝓞 K') K') y h).trans hz
  have hspan : Ideal.span {y} ^ h = (I.map (algebraMap (𝓞 K) (𝓞 K'))) ^ h := by
    rw [Ideal.span_singleton_pow, hyc, ← Ideal.map_pow, hc, Ideal.map_span, Set.image_singleton]
  have hs0 : Ideal.span {y} ≠ ⊥ := by simpa using hy0
  refine ⟨y, hy0, (GlobalTheory.CompanionTheory.Lines.ideal_eq_of_pow_eq hh hs0 ?_ hspan).symm⟩
  intro h0
  rw [h0, ← Ideal.zero_eq_bot, zero_pow hh] at hspan
  exact pow_ne_zero h hs0 hspan

theorem exists_extension_principal {ι : Type} [Fintype ι] (L : Type) [Field L] [NumberField L]
    (J : ι → Ideal (𝓞 L)) (hJ : ∀ i, J i ≠ ⊥) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : ι → 𝓞 L'),
      ∀ i, y i ≠ 0 ∧ (J i).map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y i} := by
  classical
  choose h c hh hc using fun i => GlobalTheory.UnRep.exists_pow_eq_span_singleton L (J i) (hJ i)
  let q : ι → Polynomial L := fun i => Polynomial.X ^ h i - Polynomial.C (c i : L)
  let p : Polynomial L := ∏ i, q i
  have hq0 : ∀ i, q i ≠ 0 := fun i => Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (hh i)) _
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hq0 i
  haveI : FiniteDimensional ℚ p.SplittingField := FiniteDimensional.trans ℚ L p.SplittingField
  haveI : NumberField p.SplittingField := NumberField.mk
  have hroot : ∀ i, ∃ z : p.SplittingField, z ^ h i = algebraMap L p.SplittingField (c i : L) := by
    intro i
    have hdvd : (q i).map (algebraMap L p.SplittingField) ∣ p.map (algebraMap L p.SplittingField) :=
      Polynomial.map_dvd _ (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    have hsp := (Polynomial.SplittingField.splits p).of_dvd
      (Polynomial.map_ne_zero hp0) hdvd
    have hdeg : (q i).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero (hh i))]
      exact_mod_cast hh i
    obtain ⟨z, hz⟩ := hsp.exists_eval_eq_zero (by rwa [Polynomial.degree_map])
    exact ⟨z, by simpa [q, sub_eq_zero] using hz⟩
  choose z hz using hroot
  choose y hy using fun i => span_of_root L p.SplittingField (J i) (hJ i) (h i) (hh i) (c i) (hc i)
    (z i) (hz i)
  exact ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, y, hy⟩

theorem exists_image_element {R R' B B' : Type} [CommRing R] [CommRing R'] [AddCommGroup B]
    [Module R B] [AddCommGroup B'] [Module R' B'] (φ : R →+* R') (I : Ideal R) (b : I →ₗ[R] B)
    (io : B →ₛₗ[φ] B') (x : R') (hx : x ∈ I.map φ) :
    ∃ e : B', ∀ a : I, φ a • e = x • io (b a) := by
  have hx' : x ∈ Submodule.span R' (φ '' (I : Set R)) := hx
  induction hx' using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a', ha', rfl⟩ := h
    refine ⟨io (b ⟨a', ha'⟩), fun a => ?_⟩
    have h1 : (a : R) • (⟨a', ha'⟩ : I) = a' • a := Subtype.ext (by simp [mul_comm])
    have h2 : (a : R) • b ⟨a', ha'⟩ = a' • b a := by
      rw [← b.map_smul, ← b.map_smul, h1]
    calc φ a • io (b ⟨a', ha'⟩) = io ((a : R) • b ⟨a', ha'⟩) := (io.map_smulₛₗ _ _).symm
      _ = io (a' • b a) := by rw [h2]
      _ = φ a' • io (b a) := io.map_smulₛₗ _ _
  | zero => exact ⟨0, fun a => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨e₁, h₁⟩ := hu (by assumption)
    obtain ⟨e₂, h₂⟩ := hv (by assumption)
    exact ⟨e₁ + e₂, fun a => by rw [smul_add, h₁, h₂, add_smul]⟩
  | smul r u _ hu =>
    obtain ⟨e, h⟩ := hu (by assumption)
    exact ⟨r • e, fun a => by rw [smul_comm, h, smul_smul, smul_eq_mul]⟩

theorem exists_spanning {R R' B B' ι : Type} [CommRing R] [CommRing R'] [IsDomain R']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R' B'] [Module.IsTorsionFree R' B']
    (φ : R →+* R') (I : ι → Ideal R) (b : ∀ i, I i →ₗ[R] B)
    (hsup : ⨆ i, LinearMap.range (b i) = ⊤) (io : B →ₛₗ[φ] B')
    (hspan : Submodule.span R' (Set.range io) = ⊤) (y : ι → R') (hy0 : ∀ i, y i ≠ 0)
    (hy : ∀ i, (I i).map φ = Ideal.span {y i}) :
    ∃ e : ι → B', Submodule.span R' (Set.range e) = ⊤ := by
  choose e he using fun i => exists_image_element φ (I i) (b i) io (y i)
    (by rw [hy i]; exact Ideal.mem_span_singleton_self _)
  refine ⟨e, ?_⟩
  set S := Submodule.span R' (Set.range e) with hS
  have hle : (⨆ i, LinearMap.range (b i)) ≤ S.comap io := by
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    have hmem : φ a ∈ (I i).map φ := Ideal.mem_map_of_mem φ a.2
    rw [hy i, Ideal.mem_span_singleton'] at hmem
    obtain ⟨r, hr⟩ := hmem
    have h1 := he i a
    rw [← hr, mul_comm, mul_smul] at h1
    have h2 : r • e i = io (b i a) := smul_right_injective B' (hy0 i) h1
    change io (b i a) ∈ S
    rw [← h2]
    exact S.smul_mem r (Submodule.subset_span ⟨i, rfl⟩)
  rw [hsup] at hle
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  exact hle (Submodule.mem_top (x := x))

theorem linearIndependent_of_span_card {R M ι : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype ι] (e : ι → M)
    (hs : Submodule.span R (Set.range e) = ⊤) (hc : Fintype.card ι = Module.finrank R M) :
    LinearIndependent R e := by
  classical
  let f : (ι → R) →ₗ[R] M := Fintype.linearCombination R e
  have hr : LinearMap.range f = ⊤ := by
    rw [Fintype.range_linearCombination, hs]
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [f.quotKerEquivRange.finrank_eq, hr, finrank_top, Module.finrank_pi, hc] at h1
  have h0 : Module.finrank R (LinearMap.ker f) = 0 := by omega
  have hk : LinearMap.ker f = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 h0 ⟨x, hx⟩
    have h2 : a • x = 0 := congrArg Subtype.val hax
    exact (smul_eq_zero.1 h2).resolve_left ha
  refine Fintype.linearIndependent_iff.2 fun c hcz i => ?_
  have hmem : c ∈ LinearMap.ker f := by
    simpa [f, Fintype.linearCombination_apply] using hcz
  rw [hk, Submodule.mem_bot] at hmem
  exact congrFun hmem i

theorem exists_basis_after_extension : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  intro L _ _ B _ _ _ _ I hI
  haveI : Module.IsTorsionFree (𝓞 L) B := Module.Flat.isTorsionFree
  obtain ⟨ι, _, J, b, hc, hJ, hsup⟩ := exists_ideal_cover (Module.finrank (𝓞 L) B) B rfl
  obtain ⟨L', _, _, _, y, hy⟩ := exists_extension_principal L (fun o : Option ι => o.elim I J)
    (by rintro (_ | i); exacts [hI, hJ i])
  refine ⟨L', inferInstance, inferInstance, inferInstance, y none, (hy none).2, ?_⟩
  intro B' _ _ _ _ io hspan hrk
  haveI : Module.IsTorsionFree (𝓞 L') B' := Module.Flat.isTorsionFree
  obtain ⟨e, he⟩ := exists_spanning (algebraMap (𝓞 L) (𝓞 L')) J b hsup io hspan
    (fun i => y (some i)) (fun i => (hy (some i)).1) (fun i => (hy (some i)).2)
  have hli : LinearIndependent (𝓞 L') e :=
    linearIndependent_of_span_card e he (hc.trans hrk.symm)
  let ε : Fin (Module.finrank (𝓞 L') B') ≃ ι :=
    (Fintype.equivFinOfCardEq (hc.trans hrk.symm)).symm
  refine ⟨e ∘ ε, hli.comp _ ε.injective, ?_⟩
  rw [Set.range_comp, ε.surjective.range_eq, Set.image_univ, he]

end GlobalTheory.CompanionTheory.Ar.Basis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupTangentLift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Chart

theorem one_left_spMap {S : Scheme.{0}} (G : Over S) [GrpObj G] {R A : Type} [CommRing R] [CommRing A]
    (x : Sp R ⟶ S) (g : R →+* A) :
    (1 : Over.mk (spMap g ≫ x) ⟶ G).left = spMap g ≫ (1 : Over.mk x ⟶ G).left := by
  let k : Over.mk (spMap g ≫ x) ⟶ Over.mk x := Over.homMk (spMap g) rfl
  have h : (1 : Over.mk (spMap g ≫ x) ⟶ G) = k ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (k ≫ toUnit _) (toUnit _)]
  rw [h]; rfl

theorem exists_chart_at_point (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R]
    (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime] :
    ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V)
      (hUV : U ≤ G.hom ⁻¹ᵁ V),
      RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
      ∃ u : Γ(G.left, U) →+* Localization.Away f,
        (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  let t : Sp R ⟶ G.left := (1 : Over.mk x ⟶ G).left
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  let q' : Sp R := q
  obtain ⟨V, hV, hqV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := G.hom (t q')) trivial
  obtain ⟨U, hU, hqU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := G.left) (U := G.hom ⁻¹ᵁ V) (x := t q') hqV
  have hUV' : U ≤ G.hom ⁻¹ᵁ V := hUV
  have hopen : IsOpen {y : PrimeSpectrum R | t (show Sp R from y) ∈ U} := (t ⁻¹ᵁ U).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show q ∈ _ from hqU) hopen
  refine ⟨f, hqf, U, V, hU, hV, hUV', HasRingHomProperty.appLE @Smooth G.hom inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV', ?_⟩
  let a : Sp (Localization.Away f) ⟶ Sp R := spMap (algebraMap R (Localization.Away f))
  have hrange : Set.range (a ≫ t) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    apply hsub
    have : (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) y ∈
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := ⟨y, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f] at this
    exact this
  let l := IsOpenImmersion.lift hU.fromSpec (a ≫ t) hrange
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have hl : spMap (Spec.preimage l).hom = l := by
    simp [spMap]
  rw [one_left_spMap, hl]
  exact (IsOpenImmersion.lift_fac _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.Chart
end

