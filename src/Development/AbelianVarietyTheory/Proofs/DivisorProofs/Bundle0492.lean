import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPow
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditive
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace KumNat
open ClsSpec

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) {s : ℤ} (hs : s < 0) :
    Subsingleton (Sec ((res R F).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) (p s h U x) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 α β p s h U x).2.1

variable {q : ℕ}

theorem kum_unique [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ γ' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h₁' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ' 1 0 (by simp) U x = 0)
    (h₂' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ' 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    change U ⟶ X at x
    refine sep (ClsSpec.loc_mono (root_loc (unit_res x hX) (umap x u)) fun V g ⟨v, hv⟩ => ?_)
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 0 1 _ V U g x]
    have hv' : v ^ q = umap (g ≫ x) u := by rw [hv, umap_comp]
    exact (h₂ V (g ≫ x) v hv').trans (h₂' V (g ≫ x) v hv').symm
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact (h₁ U x).trans (h₁' U x).symm
  | p + 2 =>
    haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
    exact Subsingleton.elim _ _

theorem eq_zero_of_kumT [NeZero q] (ht : kumT q = 0) {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = 0 :=
  kum_unique hX u h₁ h₂ (fun U x => ev_zero (E := sch.obj X) _ _ _ _ _)
    (fun U x v _ => (ev_zero (E := sch.obj X) _ _ _ _ _).trans (by rw [ht]; exact (smap_zero _).symm))

theorem kum_pull [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ) (hX : IsUnit (q : Γ(X, ⊤))) :
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u) := by
  obtain ⟨γ, hγ, h₁, h₂⟩ := kum_spec q hX u
  obtain ⟨γ', hγ', h₁', h₂'⟩ := kum_spec q (unit_res f hX) (umap f u)
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine Cocycle.ext (kum_unique (unit_res f hX) (umap f u) (fun U y => ?_) (fun U y v hv => ?_) h₁' h₂')
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 1 0 _ U y = 0
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 _ U y]
    exact h₁ U (y ≫ f)
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 0 1 _ U y = _
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 _ U y]
    exact h₂ U (y ≫ f) v (by rw [hv, umap_comp])

theorem kum_mul [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u₁ u₂ : (Γ(X, ⊤))ˣ) :
    kum q (u₁ * u₂) = kum q u₁ + kum q u₂ := by
  obtain ⟨γ₁, e₁, a₁, b₁⟩ := kum_spec q hX u₁
  obtain ⟨γ₂, e₂, a₂, b₂⟩ := kum_spec q hX u₂
  obtain ⟨γ₃, e₃, a₃, b₃⟩ := kum_spec q hX (u₁ * u₂)
  rw [← e₁, ← e₂, ← e₃, eq_comm, ← CohomologyClass.mk_add, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨e, he, hw⟩ := exists_two_family ht (E := sch.obj X) (p := 0) (fun U (x : U ⟶ X) => unit_res x hX)
      (fun U (x : U ⟶ X) => umap x u₁) (fun U (x : U ⟶ X) => umap x u₂)
      (fun V U g (x : U ⟶ X) => umap_comp g x u₁) (fun V U g (x : U ⟶ X) => umap_comp g x u₂)
    obtain ⟨β, c₁, c₂⟩ := exists_single (I := res _ (tw q 1)) (n := 0) 0 0 (by simp) e he
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    rw [Cocycle.coe_sub, Cocycle.coe_add, ev_sub', ev_add]
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      have hxU := unit_res (show U ⟶ X from x) hX
      refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hxU (umap (show U ⟶ X from x) u₁))
        (root_loc hxU (umap (show U ⟶ X from x) u₂))) ?_)
      rintro V g ⟨⟨v, hv⟩, w, hw'⟩
      have hv' : v ^ q = umap (show V ⟶ X from x.res g) u₁ := by rw [hv]; exact (umap_comp g _ u₁).symm
      have hw'' : w ^ q = umap (show V ⟶ X from x.res g) u₂ := by rw [hw']; exact (umap_comp g _ u₂).symm
      have hvw : (v * w) ^ q = umap (show V ⟶ X from x.res g) (u₁ * u₂) := by rw [mul_pow, hv', hw'', map_mul]
      rw [res_map, he V U g x, res_sub, res_add, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₁.1 0 1 _ V U g x,
        (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₂.1 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₃.1 0 1 _ V U g x]
      rw [hw V (x.res g) v w hv' hw'', b₁ V (x.res g) v hv', b₂ V (x.res g) w hw'', b₃ V (x.res g) _ hvw, smap_sub,
        smap_add]
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a₁ U x, a₂ U x, a₃ U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · refine ⟨0, ?_⟩
    rw [δ_zero, Cocycle.coe_sub, Cocycle.coe_add, eq_zero_of_kumT ht hX u₁ a₁ b₁, eq_zero_of_kumT ht hX u₂ a₂ b₂,
      eq_zero_of_kumT ht hX _ a₃ b₃]
    simp

theorem kum_pow_self [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) : kum q (u ^ q) = 0 := by
  obtain ⟨γ, e, a, b⟩ := kum_spec q hX (u ^ q)
  rw [← e, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨β, c₁, c₂⟩ := exists_single (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) 0 0 (by simp)
      (fun U (x : U ⟶ X) => kumT q U (umap x u))
      (fun V U g (x : U ⟶ X) => (ht.1 V U g _ (unit_res x hX)).trans (congrArg (kumT q V) (umap_comp g x u).symm))
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      change U ⟶ X at x
      exact (b U x _ (by rw [← map_pow])).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · exact ⟨0, by rw [δ_zero, eq_zero_of_kumT ht hX _ a b]⟩

end KumNat

open KumNat in

theorem kum_cocycle_natural_additive : ∀ (q : ℕ) [NeZero q], (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧ ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u → ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧ ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 := by
  intro q _
  exact ⟨fun X u hX => kum_spec q hX u, fun f u hX => kum_pull f u hX, fun u v hX => ⟨kum_mul hX u v, kum_pow_self hX u⟩⟩

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero : ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q)), (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) - freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0 → (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.relation_kernel
  | exact GlobalTheory.EtC.KummerSplit.relation_kernel
  | (intros; apply GlobalTheory.EtC.KummerSplit.relation_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelCohomologySubsingleton
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_piTensorProduct_const (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (ι : Type) [Fintype ι] : Module.Finite A (PiTensorProduct A fun _ : ι => A') := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := A')
  refine ⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : ∀ i, m i ∈ Submodule.span A (S : Set A') := fun i => hS ▸ Submodule.mem_top
  choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)
  have hm' : m = fun i => ∑ s ∈ S, c i s • s := funext fun i => ((hc i).2).symm
  rw [hm', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.coe_image]
  refine ⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩

theorem level_vanish : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn
  obtain ⟨_, e, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  have hT := GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A')
    (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn
  haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of
    (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT
  let f := disc.mapIso e
  have inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s) := fun x y h => by
    have h' := congrArg (pull (ZMod q) f.inv (tw q i) s) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h'
  exact inj.subsingleton

end GlobalTheory.EtC.GmStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevels
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LerayInj

theorem peel (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hH : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (N : ℤ) (hN : (n : ℤ) + 1 = N)
    (c : Cochain ((chains R).obj E) (res R F) N)
    (hc : ∀ (p q : ℤ) (hpq : p + N = q), p ≠ -N → c.v p q hpq = 0)
    (β₀ : Cochain ((chains R).obj E) (res R F) n) (h₀ : δ n N β₀ = c) :
    ∀ k : ℕ, k ≤ n → ∃ β : Cochain ((chains R).obj E) (res R F) n, δ n N β = c ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(k : ℤ) < p → β.v p q hpq = 0 := by
  obtain ⟨cl, -, hcl, hcl0, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  obtain ⟨-, -, -, -, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨β₀, h₀, fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨β, hβ, hv⟩ := ih (by omega)
    have hqk : (((n - k : ℕ) : ℤ)) = (n : ℤ) - k := by omega
    let t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X ((n - k : ℕ) : ℤ) :=
      (chainsXIso R E k).inv ≫ β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) (by omega)
    have ht : t ≫ (res R F).d ((n - k : ℕ) : ℤ) (((n - k : ℕ) : ℤ) + 1) = 0 := by
      have e := Cochain.congr_v hβ (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega)
      rw [δ_v n N hN β (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega) ((n - k : ℕ) : ℤ) (-(k : ℤ) + 1)
        (by omega) rfl, hc _ _ _ (by omega), hv (-(k : ℤ) + 1) (((n - k : ℕ) : ℤ) + 1) (by omega) (by omega),
        comp_zero, smul_zero, add_zero] at e
      simp only [t, Category.assoc, e, comp_zero]
    have h0 : cl _ _ t ht = cl _ _ 0 zero_comp :=
      (hH k (n - k) (by omega) (by omega) _).trans (hcl0 _ _).symm
    obtain ⟨y, hy⟩ := ((hcl _ _ _ _ _ _).1 h0)
    rw [zero_add] at hy
    let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
      Cochain.single (p := -(k : ℤ)) (q := ((n - k : ℕ) : ℤ) - 1) ((chainsXIso R E k).hom ≫ y) ((n : ℤ) - 1)
    refine ⟨β - δ ((n : ℤ) - 1) n γ, ?_, ?_⟩
    · rw [δ_sub, δ_δ, sub_zero, hβ]
    · intro p q hpq hp
      rw [Cochain.sub_v, Cochain.δ_single _ ((n : ℤ) - 1) n (by omega) (-(k : ℤ) - 1) ((n - k : ℕ) : ℤ) (by omega) (by omega),
        Cochain.add_v, Cochain.units_smul_v]
      by_cases hpk : p = -(k : ℤ)
      · subst hpk
        obtain rfl : q = ((n - k : ℕ) : ℤ) := by omega
        rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero]
        have hb : β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) hpq = (chainsXIso R E k).hom ≫ t := by
          simp only [t, Iso.hom_inv_id_assoc]
        rw [hb, hy, Category.assoc, sub_self]
      · rw [hv p q hpq (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpk,
          Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero, sub_zero]

end GlobalTheory.EtC.LerayInj

namespace GlobalTheory.EtC

theorem leray_inj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) →
    (∀ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls s 0 → s = 0) ∧
    ∀ s : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F, IsCls s 0 →
      ∃ t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd t = s := by
  intro R _ F E n hH
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  constructor
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β, hβ⟩ := hz0
    have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) 0 (by simp)
    have h1 : β.v (-((0 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    have h2 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 := (hpos E 1 (by norm_num)).eq_of_tgt _ _
    rw [δ_v m _ hm β _ 0 _ (-1) 1 (by omega) (by omega), h1, h2, zero_comp, zero_comp, smul_zero,
      add_zero] at e
    have e' : (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).hom ≫ s ≫ resι R F := by
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)) = z.1 from rfl, hz, Cochain.single_v]
    rw [e'] at e
    have e2 : s ≫ resι R F = 0 ≫ resι R F := by
      rw [zero_comp]
      exact (cancel_epi (chainsXIso R E 0).hom).1 (by rw [← e, comp_zero])
    exact (cancel_mono (resι R F)).1 e2
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β₀, hβ₀⟩ := hz0
    obtain rfl : m = (n : ℤ) := by push_cast at hm; omega
    have hzv : ∀ (p q : ℤ) (hpq : p + ((n + 1 : ℕ) : ℤ) = q),
        (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)).v p q hpq =
          (Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
            ((chainsXIso R E (n + 1)).hom ≫ s ≫ resι R F) ((n + 1 : ℕ) : ℤ)).v p q hpq := by
      intro p q hpq
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)) = z.1 from rfl, hz]
    obtain ⟨β, hβ, hv⟩ := LerayInj.peel R F E n hH ((n + 1 : ℕ) : ℤ) (by push_cast; rfl) z
      (fun p q hpq hp => by rw [hzv, Cochain.single_v_eq_zero _ _ _ _ _ hp]) β₀ hβ₀ n le_rfl

    let b := β.v (-(n : ℤ)) 0 (by omega)
    have hb : b ≫ (res R F).d 0 1 = 0 := by
      have e := Cochain.congr_v hβ (-(n : ℤ)) 1 (by push_cast; omega)
      rw [δ_v (n : ℤ) _ (by push_cast; rfl) β (-(n : ℤ)) 1 _ 0 (-(n : ℤ) + 1) (by omega) rfl,
        hv (-(n : ℤ) + 1) 1 (by omega) (by omega), comp_zero, smul_zero, add_zero, hzv,
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
      exact e
    haveI : Mono (ShortComplex.mk _ _ w).f := hmono
    let t' : ((chains R).obj E).X (-(n : ℤ)) ⟶ F := hex.lift b hb
    have ht' : t' ≫ resι R F = b := hex.lift_f b hb

    have e := Cochain.congr_v hβ (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    have h1 : β.v (-((n + 1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    rw [δ_v (n : ℤ) _ (by push_cast; rfl) β _ 0 _ (-1) (-(n : ℤ)) (by omega) (by push_cast; omega), h1,
      zero_comp, zero_add, hzv, Cochain.single_v] at e
    rw [show β.v (-(n : ℤ)) 0 (by omega) = b from rfl, ← ht'] at e
    have hD : ((chainsN R).obj E).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i) :=
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
    let D : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋n⦌)) :=
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
    have hd : ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
        (chainsXIso R E (n + 1)).hom ≫ D ≫ (chainsXIso R E n).inv :=
      (HomologicalComplex.extend_d_eq _ _ rfl rfl).trans
        (congrArg (fun D' => (chainsXIso R E (n + 1)).hom ≫ D' ≫ (chainsXIso R E n).inv) hD)
    rw [hd] at e
    have hs : s = (((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E n).inv ≫ t') := by
      apply (cancel_epi (chainsXIso R E (n + 1)).hom).1
      apply (cancel_mono (resι R F)).1
      rw [Category.assoc, ← e]
      simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    refine ⟨(((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E n).inv ≫ t'), ?_⟩
    rw [hs]
    simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
      smul_smul, Category.assoc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqSiegelParabolicOperatorEqStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.KSp.parFun_lintegral_sq | exact GlobalTheory.KSp.parFun_lintegral_sq | (intros; apply GlobalTheory.KSp.parFun_lintegral_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulEigenPartProjectionMatrixEqScalarStatement
section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K),
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeLocallyExactOfComponentSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeSec

variable {R : Type} [CommRing R]

lemma smap_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

lemma smap_add {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

lemma smap_neg {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-a) x = -Sec.map a x := rfl

lemma smap_sub {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a - b) x = Sec.map a x - Sec.map b x := rfl

lemma smap_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

lemma smap_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := (a.hom.app (op U)).hom.map_add x y

lemma smap_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := (a.hom.app (op U)).hom.map_neg x

lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

lemma smap_zero {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := (a.hom.app (op U)).hom.map_zero

lemma sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := (F.obj.map g.op).hom.map_add x y

end GlobalTheory.EtC.ConeSec

open GlobalTheory.EtC.ConeSec in

theorem GlobalTheory.EtC.cone_sec_exact : ∀ (R : Type) [CommRing R] {I J : Cx R} (f : I ⟶ J) (U : Scheme.{0}) (n : ℤ), (∀ (b₁ : Sec (I.X (n + 1)) U) (b₂ : Sec (J.X n) U), Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 → Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec (I.X n) V) (a₂ : Sec (J.X (n - 1)) V), Sec.map (I.d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map (f.f n) a₁ + Sec.map (J.d (n - 1) n) a₂ = Sec.res g b₂) → ∀ b : Sec ((mappingCone f).X n) U, Sec.map ((mappingCone f).d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec ((mappingCone f).X (n - 1)) V, Sec.map ((mappingCone f).d (n - 1) n) a = Sec.res g b := by
  intro R _ I J f U n hyp b hb
  obtain ⟨b₁, hb₁⟩ : ∃ x, Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) b = x := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x, Sec.map ((mappingCone.snd f).v n n (add_zero n)) b = x := ⟨_, rfl⟩
  have h1 : Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_fst_v f n (n + 1) (n + 2) rfl (by ring))
    simp only [smap_comp, smap_neg, hb, smap_zero, hb₁] at e
    exact neg_eq_zero.mp e.symm
  have h2 : Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_snd_v f n (n + 1) rfl)
    simp only [smap_comp, smap_add, hb, smap_zero, hb₁, hb₂] at e
    exact e.symm
  have hid := congrArg (fun φ => Sec.map φ b) (mappingCone.id_X f n (n + 1) rfl)
  simp only [smap_comp, smap_add, smap_id, hb₁, hb₂] at hid
  obtain ⟨S, hS, h⟩ := hyp b₁ b₂ h1 h2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a₁, a₂, e1, e2⟩ := h V g hg
  refine ⟨Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁ + Sec.map ((mappingCone.inr f).f (n - 1)) a₂, ?_⟩
  have k1 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (f.f n) a₁) -
        Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.map (I.d n (n + 1)) a₁) := by
    rw [← smap_comp, mappingCone.inl_v_d f n (n - 1) (n + 1) (by ring) (by ring), smap_sub, smap_comp, smap_comp]
  have k2 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inr f).f (n - 1)) a₂) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (J.d (n - 1) n) a₂) := by
    rw [← smap_comp, mappingCone.inr_f_d, smap_comp]
  have k3 : Sec.res g b = Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.res g b₁) +
      Sec.map ((mappingCone.inr f).f n) (Sec.res g b₂) := by
    rw [← hid, sres_add, sres_map, sres_map]
  rw [smap_add', k1, k2, e1, k3, ← e2, smap_add', smap_neg']
  abel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCoverStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayerVietoris_equivalence_of_cover : GlobalTheory.EtC.A4 := by
  first | (exact @GlobalTheory.MayerVietorisEqv.a4) | (exact GlobalTheory.MayerVietorisEqv.a4) | (intros; apply GlobalTheory.MayerVietorisEqv.a4  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPowStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ), IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.HeckeLBound.norm_heckeL_le | exact GlobalTheory.HeckeLBound.norm_heckeL_le | (intros; apply GlobalTheory.HeckeLBound.norm_heckeL_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormsTwoCocycleCoboundaryOfRestrictStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict (FormExt.omExt F) G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) := by
  first | exact @GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms | exact GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms | (intros; apply GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsionStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qConj_torsion_points : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), ZetaAct g N a → ∀ x : Fin 2 → ZMod N, QConj g N (wp N x) (wp N (vmul x (dg a))) ∧ QConj g N (wpd N x) (wpd N (vmul x (dg a))) ∧ (x ≠ 0 → QConj g N (wB N x) (wB N (vmul x (dg a)))) := by
  first | exact @GlobalTheory.WpFam.ConjExp.qConj_torsion | exact GlobalTheory.WpFam.ConjExp.qConj_torsion | (intros; apply GlobalTheory.WpFam.ConjExp.qConj_torsion <;> assumption)
end

