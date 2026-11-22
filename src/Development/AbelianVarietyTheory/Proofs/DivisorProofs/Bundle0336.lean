import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.GradedWeylDivisibility.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCElements

theorem chains_X_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) :=
  ((chainsN R).obj E).isZero_extend_X ComplexShape.embeddingDownNat n (fun i hi => by
    change -(i : ℤ) = n at hi; omega)

theorem res_X_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  intro R _ F
  have zero_iff : ∀ (E : Spc) (n : ℤ) (c : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk c = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), (show ((HC R F).obj (op E)).X n from c.1) = ((HC R F).obj (op E)).d (n - 1) n y := by
    intro E n c
    rw [CohomologyClass.mk_eq_zero_iff]
    constructor
    · rintro ⟨m, hm, β, hβ⟩
      obtain rfl : m = n - 1 := by omega
      exact ⟨β, hβ.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨n - 1, by omega, y, hy.symm⟩
  refine ⟨?_, fun E n z hz => CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz), ?_, ?_, ?_, ?_⟩
  · intro E n hn
    refine @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => ?_⟩
    change Cochain ((chains R).obj E.unop) (res R F) n at a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : 0 < p
    · exact (chains_X_isZero R E.unop p hp).eq_of_src _ _
    · exact (res_X_isZero R F q (by omega)).eq_of_tgt _ _
  · intro E n x
    obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c.1, c.2, rfl⟩
  · intro E n z hz z' hz'
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _ at hy
      rw [← hy]; abel
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _
      rw [hy]; abel
  · intro E n z hz
    exact zero_iff E n _
  · intro E E' f n z hz
    refine ⟨(zcomp (Cocycle.ofHom ((chains R).map f)) (Cocycle.mk z (n + 1) rfl hz) (zero_add n)).2, ?_⟩
    rfl

end GlobalTheory.EtC.HCElements
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwist
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem mem_coinv_of_finset_sum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (R : Finset (GL (Fin a) k)) (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) (hχ : IsLocallyConstant χ)
    (h1 : ∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y)
    (h2 : ∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) : Φ ∈ coinv ν β a (a + b) := by
  set H : GL (Fin a) k → Matrix (Fin a) (Fin (a + b)) k → ℂ :=
    fun r Y => χ Y * (tw ν (a + b) r * Φ (r.val * Y)) with hH
  have hHSB : ∀ r, H r ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
    intro r
    have hs : (fun Y => Φ (r.val * Y)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
      have := comp_mul_mem_SB r 1 hΦ
      simp only [Units.val_one, Matrix.mul_one] at this
      exact this
    obtain ⟨hs1, hs2⟩ := hs
    have e : H r = χ * ((fun _ => tw ν (a + b) r) * fun Y => Φ (r.val * Y)) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · exact hχ.mul ((IsLocallyConstant.const _).mul hs1)
    · exact HasCompactSupport.mul_left (HasCompactSupport.mul_left hs2)
  have hom : ∀ r, omA ν β r 1 (H r) = fun Y => χ ((r⁻¹).val * Y) * Φ Y := by
    intro r
    funext Y
    rw [omA_one_apply]
    simp only [hH, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    field_simp [tw_ne_zero ν (a + b) r]
  have hsumH : ∑ r ∈ R, H r = 0 := by
    funext Y
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [hH, ← Finset.mul_sum]
    exact h2 Y
  have hΦeq : Φ = ∑ r ∈ R, (omA ν β r 1 (H r) - H r) := by
    rw [Finset.sum_sub_distrib, hsumH, sub_zero]
    funext Y
    rw [Finset.sum_apply]
    simp only [hom]
    exact h1 Y
  rw [hΦeq]
  refine Submodule.sum_mem _ fun r _ => Submodule.subset_span ⟨r, H r, hHSB r, rfl⟩

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory

open scoped Pointwise

theorem compact_finite_leftCoset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  intro G _ _ _ K hK C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Finset.mem_image] at hr hr'
    obtain ⟨a, -, rfl⟩ := hr
    obtain ⟨b, -, rfl⟩ := hr'
    have h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b) :=
      QuotientGroup.eq.2 hrr'
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro g hg
    have hm := ht hg
    simp only [Set.mem_iUnion] at hm
    obtain ⟨gi, hgi, hmem⟩ := hm
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩
    have h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [smul_eq_mul, mul_assoc] using K.mul_mem h1 hk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimits
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContFin

theorem term_preserves (N : CommRingCat.{0} ⥤ AbCx) (hN : PreservesFilteredColimitsOfSize.{0, 0} N) (n : ℤ) :
    PreservesFilteredColimitsOfSize.{0, 0} (term N n) := by
  constructor
  intro J _ _
  unfold term
  have : PreservesColimitsOfShape J N := hN.preserves_filtered_colimits J
  infer_instance

theorem cohomology_filteredColimit : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  intro N hN
  refine ⟨term_preserves N hN, ?_⟩
  intro J _ _ D c hc n
  have E : ∀ m : ℤ, (∀ x : ((N).obj c.pt).X m, ∃ j y, ((N).map (c.ι.app j)).f m y = x) ∧
      ∀ j (y : ((N).obj (D.obj j)).X m), ((N).map (c.ι.app j)).f m y = 0 → ∃ (k : J) (f : j ⟶ k), ((N).map (D.map f)).f m y = 0 :=
    fun m => ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N m)).mp (term_preserves N hN m)) J D c hc

  have nat : ∀ {a b : CommRingCat.{0}} (g : a ⟶ b) (p q : ℤ) (x : ((N).obj a).X p),
      ((N).map g).f q (((N).obj a).d p q x) = ((N).obj b).d p q (((N).map g).f p x) := by
    intro a b g p q x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ((N).map g).comm]
  have mapf : ∀ {j k : J} (f : j ⟶ k) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (c.ι.app k)).f m (((N).map (D.map f)).f m x) = ((N).map (c.ι.app j)).f m x := by
    intro j k f m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, c.w f]
  have mapcomp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (D.map (f ≫ g))).f m x = ((N).map (D.map g)).f m (((N).map (D.map f)).f m x) := by
    intro j k l f g m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← D.map_comp]
  constructor
  · intro z hz
    obtain ⟨j, w, hw⟩ := (E n).1 z
    have h1 : ((N).map (c.ι.app j)).f (n + 1) (((N).obj (D.obj j)).d n (n + 1) w) = 0 := by
      rw [nat, hw]
      exact hz
    obtain ⟨k, f, hf⟩ := (E (n + 1)).2 j _ h1
    refine ⟨k, ((N).map (D.map f)).f n w, 0, ?_, ?_⟩
    · rw [← nat, hf]
    · rw [mapf, hw, map_zero, add_zero]
  · intro j w _ ⟨y, hy⟩
    obtain ⟨j', y', rfl⟩ := (E (n - 1)).1 y
    let k := IsFiltered.max j j'
    let fa : j ⟶ k := IsFiltered.leftToMax j j'
    let fb : j' ⟶ k := IsFiltered.rightToMax j j'
    set u := ((N).map (D.map fa)).f n w - ((N).obj (D.obj k)).d (n - 1) n (((N).map (D.map fb)).f (n - 1) y') with hu
    have h0 : ((N).map (c.ι.app k)).f n u = 0 := by
      rw [hu, map_sub, mapf, ← nat, mapf, hy, nat]
      exact sub_self _
    obtain ⟨l, g, hg⟩ := (E n).2 k u h0
    refine ⟨l, fa ≫ g, ((N).map (D.map g)).f (n - 1) (((N).map (D.map fb)).f (n - 1) y'), ?_⟩
    rw [hu, map_sub, sub_eq_zero] at hg
    rw [mapcomp, hg, nat]

end GlobalTheory.EtC.ContFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeqExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeSeq

variable {R : Type} [CommRing R]

theorem cls_eq {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeSeq

theorem GlobalTheory.EtC.coneSeq_exact : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ), Function.Exact (cpull (mappingCone.inr f) I n) (cpull f I n) ∧ Function.Exact (cpull f I n) (cpre (mappingCone.fst f) I n (n + 1) (by omega)) ∧ Function.Exact (cpre (mappingCone.fst f) I n (n + 1) (by omega)) (cpull (mappingCone.inr f) I (n + 1)) := by
  intro R _ K L f I n
  refine ⟨?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hb
      obtain ⟨b, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ b _) = 0 at hb
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb
      obtain ⟨β, hβ⟩ := hb
      refine ⟨CohomologyClass.mk (mappingCone.descCocycle f (n.negOnePow • β) b (by omega) ?_), ?_⟩
      · rw [δ_units_smul, hβ]; simp [zcomp]
      · change CohomologyClass.mk (zcomp _ _ _) = _
        congr 1; ext1; simp [zcomp]
    · rintro ⟨z, rfl⟩
      obtain ⟨c, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ c _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • (mappingCone.inl f).comp (c : Cochain _ I n) (by omega), ?_⟩
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul]
  · intro y
    constructor
    · intro ha
      obtain ⟨a, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ a _) = 0 at ha
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at ha
      obtain ⟨γ, hγ⟩ := ha
      have hβ : δ n (n + 1) ((Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n)) = 0 := by
        rw [δ_ofHom_comp, hγ]; simp [zcomp]
      refine ⟨CohomologyClass.mk (Cocycle.mk (-(n.negOnePow • (Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n))) (n + 1) rfl (by rw [δ_neg, δ_units_smul, hβ]; simp)), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ (n - 1) (by omega) (-((mappingCone.inl f).comp γ (by omega))) ?_
      have key := δ_comp (mappingCone.inl f) γ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) rfl
      rw [hγ] at key
      simp [zcomp] at key
      simp [zcomp, key, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    · rintro ⟨z, rfl⟩
      obtain ⟨b, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ b _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      refine ⟨-(n.negOnePow • (mappingCone.snd f).comp (b : Cochain _ I n) (zero_add n)), ?_⟩
      rw [δ_neg, δ_units_smul, δ_comp _ _ _ 1 (n + 1) (n + 1) rfl (zero_add 1) rfl]
      simp [zcomp, smul_smul, Cochain.comp_assoc_of_second_is_zero_cochain]
  · intro y
    constructor
    · intro hc
      obtain ⟨c, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ c _) = 0 at hc
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at hc
      obtain ⟨β, hβ⟩ := hc
      set a : Cochain K I n := (mappingCone.inl f).comp (c : Cochain _ I (n + 1)) (by omega) +
        n.negOnePow • (Cochain.ofHom f).comp β (zero_add n) with ha_def
      have hsnd := δ_comp (mappingCone.snd f) β (zero_add n) 1 (n + 1) (n + 1) rfl (zero_add 1) rfl
      rw [hβ] at hsnd
      simp [zcomp] at hsnd
      have hdec : (c : Cochain _ I (n + 1)) = (mappingCone.fst f).1.comp a (by omega) +
          δ n (n + 1) ((mappingCone.snd f).comp β (zero_add n)) := by
        rw [mappingCone.ext_cochain_from_iff f n (n + 1) rfl]
        constructor
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
      have hcoc : δ n (n + 1) a = 0 := by
        have h1 := congrArg (δ (n + 1) (n + 2)) hdec
        rw [δ_add, δ_δ, add_zero, Cocycle.δ_eq_zero c (n + 2)] at h1
        rw [δ_comp _ _ _ 2 (n + 1) (n + 2) (by omega) rfl rfl] at h1
        simp at h1
        have h2 := congrArg (fun x => (mappingCone.inl f).comp x (show -1 + (n + 2) = n + 1 by omega)) h1
        simpa using h2.symm
      refine ⟨CohomologyClass.mk (Cocycle.mk a (n + 1) rfl hcoc), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ n rfl (-((mappingCone.snd f).comp β (zero_add n))) ?_
      simp [zcomp, hdec]
    · rintro ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ a _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      exact ⟨0, by simp [zcomp]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormDegZeroCocycleClosedStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectionForm_degZeroCocycle_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  first | exact @GlobalTheory.AnPer.ClosedSq.connForm_closed | exact GlobalTheory.AnPer.ClosedSq.connForm_closed | (intros; apply GlobalTheory.AnPer.ClosedSq.connForm_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionIntegral
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem nhds_one_slice_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB k a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice k a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcpt⟩, hrk⟩ := hΦ

  have hcl : IsClosed (Function.support Φ) := by
    have : Function.support Φ = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this, isClosed_compl_iff]; exact hlc.isOpen_fiber 0
  have hS : tsupport Φ ⊆ {Y | Y.rank = a} := by
    intro Y hY
    rw [tsupport, hcl.closure_eq] at hY
    by_contra h; exact hY (hrk Y h)
  set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k :=
    fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf
  have hfc : ContinuousOn f (tsupport Φ) := by
    have hs' := hs.mono hS
    refine ContinuousOn.prodMk hs' ?_
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn
      ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)
  have hA : IsCompact (f '' tsupport Φ) := hcpt.image_of_continuousOn hfc
  set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) :=
    {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn
  have hno : IsOpen n := by
    have h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.2.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    have h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    exact (h1.prodMk h2) {q | q.1 = q.2}
  have hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n := by
    rintro ⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [hn]
  obtain ⟨u, v, -, hv, hAu, h1v, huv⟩ := generalized_tube_lemma hA isCompact_singleton hno hsub

  have key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice k a d → Φ (h.val * Z) ≠ 0 →
      (h, Z) ∈ f '' tsupport Φ := by
    intro h Z hZ hne
    have hY : h.val * Z ∈ tsupport Φ := subset_tsupport _ hne
    have hr := hS hY
    have e : (s (h.val * Z))⁻¹ * h = 1 := by
      apply huniq Z _ hZ
      have := hsl _ hr
      simpa [Units.val_mul, Matrix.mul_assoc] using this
    have e' : s (h.val * Z) = h := by
      have := congrArg (fun t => s (h.val * Z) * t) e
      simpa [mul_assoc] using this.symm
    refine ⟨h.val * Z, hY, ?_⟩
    simp only [hf, e', Prod.mk.injEq, true_and]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩
  · exact (hv.inv).mem_nhds (by simpa using h1v rfl)
  rintro x ⟨hxv, hxv'⟩ g Z hZ
  by_cases h0 : Φ (g.val * Z) ≠ 0
  · exact huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)
  by_cases h0' : Φ (g.val * x.val * Z) ≠ 0
  · have hm : (g * x, Z) ∈ f '' tsupport Φ := key (g * x) Z hZ (by simpa [Units.val_mul] using h0')
    have := huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))
    simp only [hn, Set.mem_setOf_eq] at this
    rw [Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at this
    rw [this]
  push_neg at h0 h0'
  rw [h0, h0']

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionMeasure
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem exists_isCompact_of_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB k a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice k a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcs⟩, hrank⟩ := hΦ
  have hclosed : IsClosed (Function.support Φ) := by
    exact (hlc.isClopen_fiber (0 : ℂ)).compl.isClosed
  have hts : tsupport Φ = Function.support Φ := hclosed.closure_eq
  have hsub : tsupport Φ ⊆ {Y | Y.rank = a} := by
    intro Y hY
    rw [hts] at hY
    by_contra h
    exact hY (hrank Y h)
  refine ⟨s '' tsupport Φ, hcs.isCompact.image_of_continuousOn (hs.mono hsub), ?_⟩
  intro g Z hZ hne
  have hY : g.val * Z ∈ tsupport Φ := subset_tsupport _ hne
  have hr : (g.val * Z).rank = a := hsub hY
  have h1 : ((s (g.val * Z))⁻¹ * g).val * Z ∈ slice k a d := by
    rw [Units.val_mul, Matrix.mul_assoc]
    exact hsl _ hr
  have h2 := huniq Z _ hZ h1
  have : g = s (g.val * Z) := by
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  exact ⟨g.val * Z, hY, this.symm⟩

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

def defect (Q q : ℕ) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  (redMap Q q 1).app U 0 (kumT Q U v) - kumT q U (v ^ (Q / q))

def defectSec (Q q : ℕ) (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  pick fun s => ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
    Sec.res g s = defect Q q V v

def corrFam (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 1, s, h, U, x => Sec.map ((res _ (tw q 1)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (defectSec Q q U (lineUnit L x))
  | _, _, _, _, _ => 0

theorem corrFam_zero (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E 0 U) : corrFam Q q L 0 s h U x = 0 := rfl

theorem corrFam_add_two (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : corrFam Q q L (p + 2) s h U x = 0 := rfl

theorem corrFam_one (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : corrFam Q q L 1 0 h U x = defectSec Q q U (lineUnit L x) := by
  simp [corrFam, Sec.map]

end GlobalTheory.EtC.RedChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRestrictScalarsTwoSidedMatrixMulStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E), (∀ x, T x = u * x * a) → LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  first | exact @GlobalTheory.KSp.det_restrictScalars_twoSidedMul | exact GlobalTheory.KSp.det_restrictScalars_twoSidedMul | (intros; apply GlobalTheory.KSp.det_restrictScalars_twoSidedMul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylEqBotOfNotAntitoneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_eq_bot_of_not_antitone' : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ), ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  first | exact @GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone | exact GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone | (intros; apply GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantProductOrdersStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_determinant_product_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (a b h : ℕ) (D : Datum ε h Λ) (τ : Λ →+* O) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → ∃ x : Fin (a + b) → eig C (actT D) τ, (∀ i, (x (Fin.castAdd b i) : Fin h → C) = w i) ∧ (∀ i, alC C D (x (Fin.natAdd a i)) = n i) ∧ IsBasisOf C (eigPart C (actT D) τ ⊤) (fun i => (x i : Fin h → C)) ∧ detLattice C (actT D) τ (a + b) = Submodule.span O {exteriorPower.ιMulti C (a + b) x} := by
  first | exact @GlobalTheory.ShiftBasis.shift_basis | exact GlobalTheory.ShiftBasis.shift_basis | (intros; apply GlobalTheory.ShiftBasis.shift_basis <;> assumption)
end

