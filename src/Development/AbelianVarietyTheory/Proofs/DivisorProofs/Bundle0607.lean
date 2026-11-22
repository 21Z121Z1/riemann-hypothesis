import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSuppSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CupAssoc

def trPair {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) :
    Pair I J (res _ (tw q k')) := h ▸ μ

theorem trPair_isTwPair {q : ℕ} {i j k k' : ℤ} (h : k = k') (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (hμ : IsTwPair μ) : IsTwPair (trPair h μ) := by
  subst h; exact hμ

theorem trPair_cup {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) (E : Spc)
    {n m w : ℤ} (hw : n + m = w) (a : CohomologyClass ((chains _).obj E) I n) (b : CohomologyClass ((chains _).obj E) J m) :
    (trPair h μ).cup E hw a b = Ht.cast hw h (μ.cup E rfl a b) := by
  subst h; subst hw; rfl

theorem secMap_id {R : Type} [CommRing R] (K : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (K.X s) U) :
    Sec.map (HomologicalComplex.Hom.f (𝟙 K) s) x = x := rfl

theorem main : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  intro q _ E n m k i j l a b c
  have hk : i + (j + l) = i + j + l := by ring
  have hd : n + (m + k) = n + m + k := by ring

  set μ := twPair q i j with hμdef
  set P := twPair q (i + j) l with hPdef
  set μ' := twPair q j l with hμ'def
  set Q' := trPair hk (twPair q i (j + l)) with hQ'def
  have hμ : IsTwPair μ := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1
  have hP : IsTwPair P := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q (i + j) l).1
  have hμ' : IsTwPair μ' := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q j l).1
  have hQ' : IsTwPair Q' := trPair_isTwPair hk _ (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i (j + l)).1
  have hfun := GlobalTheory.EtC.ZcFun.main (ZMod q)
  have cpush_id : ∀ (K I : Cx (ZMod q)) (n : ℤ) x, cpush K (𝟙 I) n x = x := fun K I n x => ((hfun.1 K I n x).2)

  obtain ⟨hIi, hFi, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hIj, hFj, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  obtain ⟨hIl, hFl, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q l
  obtain ⟨-, -, hext⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j + l)
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) T (res _ (tw q l))
  have hT := GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hIi hIj hFj τ hτ
  have hT3 := GlobalTheory.T.isTateTwistResolution_tensor_flat q (i + j) l (i + j + l) rfl _ _ hT hIl hFl τ' hτ'

  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 P u (𝟙 _)
  have L1 : μ.cup E rfl a b = cpush _ u (n + m) (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ μ (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
  have L2 : P.cup E rfl (cpush _ u (n + m) (τ.cup E rfl a b)) c = cpush _ u₁ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' P u (𝟙 _) u₁ hu₁ E rfl _ c, cpush_id]

  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_sheafComplexPairing_tensor_assoc_desc (ZMod q) τ τ' hτ hτ' μ' Q'
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 ν (𝟙 _) (𝟙 _)
  have R1 : ν.cup E rfl (τ.cup E rfl a b) c = Q'.cup E hd a (μ'.cup E rfl b c) :=
    GlobalTheory.T.cupProduct_assoc_of_pairing_assoc (ZMod q) τ ν μ' Q' hν E rfl rfl rfl hd a b c
  have R2 : cpush _ u₂ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) = ν.cup E rfl (τ.cup E rfl a b) c := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' ν (𝟙 _) (𝟙 _) u₂ hu₂ E rfl _ c, cpush_id, cpush_id]

  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (u₁.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) =
      Sec.map (u₂.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) := by
    intro U ζ
    rw [hu₁, hu₂]
    try simp only [secMap_id]
    rw [hu]
    try simp only [secMap_id]
    rw [hμ U ζ, hP U ζ, hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0), hμ' U ζ, hQ' U ζ]
  obtain ⟨hH⟩ := (hext _ hT3).2 u₁ u₂ hgen
  have hpush := ((hfun.2.2.2.2 u₁ u₂ ⟨hH⟩) ((chains _).obj E) (n + m + k)).2

  show P.cup E rfl (μ.cup E rfl a b) c = _
  rw [L1, L2, hpush, R2, R1, hQ'def, trPair_cup]
  rfl

end GlobalTheory.EtC.CupAssoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedComm
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_eq_cast_of_isTwPair (q : ℕ) [NeZero q] (E : Spc) {n m i j k w : ℤ} (hk : i + j = k) (hw : n + m = w)
    (ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (hν : IsTwPair ν) (a : Ht q E n i) (b : Ht q E m j) :
    ν.cup E hw a b = (cup q a b).cast hw hk := by
  subst hk
  subst hw
  have h := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).2 (i + j) rfl ν (twPair q i j) hν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 E (n := n) (m := m) rfl
  rw [h]
  rfl

theorem isTwPair_of_isFlip (q : ℕ) {i j k : ℤ} (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hμ : IsTwPair μ) (h : μ.IsFlip ν) : IsTwPair ν := by
  intro U ζ
  rw [h U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ), hμ U ζ]
  simp

theorem cup_comm (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j) :
    cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  obtain ⟨ν, hf, -, -⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) (twPair q i j)
  have hν : IsTwPair ν := isTwPair_of_isFlip q _ ν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 hf
  have h1 := GlobalTheory.T.cup_graded_comm_of_isFlip (ZMod q) (twPair q i j) ν hf E (n := n) (m := m) (k := n + m) rfl (by ring) a b
  have h2 := cup_eq_cast_of_isTwPair q E (n := m) (m := n) (i := j) (j := i) (k := i + j) (w := n + m) (by ring) (by ring) ν hν b a
  change (twPair q i j).cup E rfl a b = _
  rw [h1, h2]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClasses
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CupGen
open ClsSpec

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem aw_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {m : ℤ} (hm : 0 + m = m)
    (hI : ∀ (s : ℤ) (U : Scheme.{0}), s < 0 → Subsingleton (Sec (I.X s) U))
    (α : Cochain ((chains R).obj E) I 0) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K m)
    (h : μ.IsAW hm α β γ) (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + m = w) (U : Scheme.{0}) (x : Sx E N U) :
    ev γ N w hw U x = μ.mul U 0 w w (zero_add w) (ev α 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β N w hw U x) := by
  rw [h N w hw U x, Finset.sum_eq_single 0]
  · subst hw
    have e1 : ((m * (((0 : Fin (N + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub ((0 : Fin (N + 1)) : ℕ) (N - ((0 : Fin (N + 1)) : ℕ)) (by simp) = x := sub_zero_full x (by omega)
    rw [e2]
    rfl
  · intro p _ hp
    have hp' : 0 < (p : ℕ) := Fin.pos_iff_ne_zero.2 hp
    haveI := hI (-((p : ℕ) : ℤ) + 0) U (by omega)
    rw [Subsingleton.elim (ev α p _ rfl U _) 0, map_zero, LinearMap.zero_apply, smul_zero]
  · intro h0; exact absurd (Finset.mem_univ _) h0

theorem factor_cochain {R : Type} [CommRing R] {E : Spc} {D C : Cx R} (ι : D ⟶ C)
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) {n : ℤ} (β : Cochain ((chains R).obj E) C n)
    (hβ : ∀ p s h U x, ∃ b, Sec.map (ι.f s) b = ev β p s h U x) :
    ∃ β' : Cochain ((chains R).obj E) D n, β'.comp (Cochain.ofHom ι) (add_zero n) = β := by
  choose b hb using hβ
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := E) (I := D) (n := n) b (fun p s h V U g x => by
    apply hinj
    rw [← res_map, hb, hb, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.1])
  refine ⟨β', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => ?_⟩
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.2, hβ', hb]

theorem supp_twres (q : ℕ) [NeZero q] (i : ℤ) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U)))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (D.X 0) U, IsTwRes q i D e ∧
      ∀ U ζ, Sec.map (ι.f 0) (e U ζ) = resGen i ζ := GlobalTheory.T.supportedSections_tateTwist_resolution q i D ι hinj hD

theorem exists_unit_map (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
    (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U),
      Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := GlobalTheory.T.unitSection_multiplication_chainMap q i k μ D ι hD

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem root_mul (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ) :
    cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧
      rootClass 0 ζ = one q (sch.obj X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec i ζ
    obtain ⟨β, hβ, hβv⟩ := rootClass_spec j ζ
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).1 α β
    have hc := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).2 α β γ hγ
    change (twPair q i j).cup (sch.obj X) rfl (rootClass i ζ) (rootClass j ζ) = rootClass (i + j) ζ
    rw [← hα, ← hβ, hc, (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2]
    refine ((GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q (i + j)) X).1 _ γ).1 ?_
    have e := hγ 0 0 (by simp) X (𝟙 X)
    rw [Finset.sum_eq_single 0 (fun p _ hp => absurd (Subsingleton.elim (α := Fin 1) p 0) hp) (fun h0 => absurd (Finset.mem_univ _) h0)] at e
    have e1 : (((0 : ℤ) * (((0 : Fin 1) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul] at e
    refine e.trans ?_
    have a1 := hαv X (𝟙 X)
    have b1 := hβv X (𝟙 X)
    rw [res_id] at a1 b1
    change (twPair q i j).mul X 0 0 0 (add_zero 0) (ev α.1 0 0 (by simp) X (𝟙 X)) (ev β.1 0 0 (by simp) X (𝟙 X)) = _
    rw [a1, b1]
    exact (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 X ζ
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec 0 ζ
    have hE : Inv q (sch.obj X) := fun U ⟨x⟩ => unit_res (x : U ⟶ X) ζ.2.1
    rw [← hα]
    refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 _ hE α fun U x ξ => ?_
    refine (hαv U x).trans ?_
    exact (res_resGen (q := q) 0 (show U ⟶ X from x) ζ).trans (resGen_zero_eq _ _)

theorem one_mul_of_pair (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E) (n i : ℤ) (hn : 0 + n = n)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i))) (hμ : IsTwPair μ) (a : Ht q E n i) :
    μ.cup E hn (one q E) a = a := by
  obtain ⟨α, hα1, hαv⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).1 E hE
  obtain ⟨β, rfl⟩ := a.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).1 α β
  rw [← hα1, (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).2 α β γ hγ]
  obtain ⟨D, ι, hinj, hD⟩ := GlobalTheory.EtC.SuppSub.exists_supp_sub (ZMod q) (res _ (tw q i))
    (fun U => IsUnit (q : Γ(U, ⊤))) (fun V U g h => unit_res g h)
  obtain ⟨e, he, heι⟩ := supp_twres q i D ι hinj hD
  obtain ⟨u, hu⟩ := exists_unit_map q i i μ D ι hD
  have hom : Nonempty (Homotopy u ι) := ((GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i).2.2 e he).2 u ι fun U ζ => by
    rw [hu U ζ 0 (e U ζ), heι]
    exact hμ U ζ

  have hunit : ∀ (p : ℕ) (U : Scheme.{0}) (x : Sx E p U), IsUnit (q : Γ(U, ⊤)) :=
    fun p U x => hE U ⟨x.sub 0 0 (by omega)⟩
  obtain ⟨β', hβ'⟩ := factor_cochain ι hinj β.1 fun p s h U x =>
    (hD s U _).2 (loc_all fun V g => Or.inl (unit_res g (hunit p U x)))
  have hδ : δ n (n + 1) β' = 0 := by
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => hinj s U ?_
    rw [← (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, ← δ_comp_ofHom, hβ', Cocycle.δ_eq_zero, ev_zero, ev_zero, smap_zero]
  set β'' : Cocycle ((chains (ZMod q)).obj E) D n := Cocycle.mk β' (n + 1) rfl hδ
  have hb : CohomologyClass.mk β = cpush _ ι n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    exact Cocycle.ext hβ'.symm
  have hg : CohomologyClass.mk γ = cpush _ u n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun N w hw U x => ?_)
    change ev γ.1 N w hw U x = ev (β'.comp (Cochain.ofHom u) (add_zero n)) N w hw U x
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, aw_zero_left μ hn (fun s U hs => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs)
      α.1 β.1 γ.1 hγ N w hw U x]
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hunit N U x)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hu V ζ w, ← hβ', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2,
      μ.nat g, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hαv V _ ζ]
  rw [hb, hg, ((GlobalTheory.EtC.ZcFun.main (ZMod q)).2.2.2.2 u ι hom _ n).2]

theorem main : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  intro q _
  refine ⟨fun E hE => ?_, fun X ζ i j => root_mul q X ζ i j⟩
  intro n i a
  have key : ∀ (k : ℤ) (hk : i = k) (m : ℤ) (hm : 0 + n = m) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k))),
      IsTwPair μ → μ.cup E hm (one q E) a = a.cast (by omega) hk := by
    intro k hk m hm μ hμ
    subst hk
    obtain rfl : m = n := by omega
    exact one_mul_of_pair q E hE _ i hm μ hμ a
  exact key (0 + i) (by ring) (0 + n) rfl (twPair q 0 i) ((GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q 0 i).1)

end GlobalTheory.EtC.CupGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPow
section
namespace GlobalTheory.EtC

theorem kummer_divisor_step : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro q k B _ _ _ _ _ _ hq f hf A₂ _ _ hA c
  obtain ⟨b₁, m, e, he, hc⟩ := GlobalTheory.T.exists_unit_form_localization_etale_nbhd B A₂ f hA c
  by_cases hb : b₁ = 0
  · refine ⟨1, isCoprime_one_right, 1, ?_, ⟨B, inferInstance, inferInstance, isExcisionNbhd_self B 1, 1, by simp⟩⟩
    have hL := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA e 1 (by simpa using he)
    refine ⟨Localization.Away e, inferInstance, inferInstance, inferInstance, inferInstance, hL, by simp, 1, ?_⟩
    intro φ ψ hφ hψ
    subst hb
    have hc' := congrArg φ hc
    simp only [map_zero, map_mul, map_pow] at hc'
    have hx : IsUnit (φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) e) *
        φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f)) ^ m) := by
      have h1 : ∀ y : A₂, φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) y) =
          algebraMap (Localization.Away e) _ (algebraMap A₂ (Localization.Away e) y) := fun y => by
        rw [← RingHom.comp_apply, hφ]; rfl
      rw [h1, h1]
      refine IsUnit.mul ((IsLocalization.Away.algebraMap_isUnit e).map _) (IsUnit.pow _ ?_)
      rw [← IsScalarTower.algebraMap_apply]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (Localization.Away e) f)) (algebraMap B (Localization.Away e) f)
    have hu := (c.isUnit.map φ).mul hx
    rw [← hc'] at hu
    haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
    exact Subsingleton.elim _ _
  · obtain ⟨g, hg0, hfg, u, n, d, t, n', d', hn, hd, hn', hd', h1, h2⟩ := GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition k B q hq f hf b₁ hb m
    exact ⟨g, hfg, u, GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus k B q hq f hf A₂ hA c b₁ m e he hc g hfg u n d hn hd h1,
      GlobalTheory.T.coprime_unit_etale_extension k B q hq f g hg0 u t n' d' hn' hd' h2⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
noncomputable section

namespace GlobalTheory.HomFixMat

abbrev powPull {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => a)

theorem wchart_comp_le {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f ≫ φ) j ≤ f ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j := by
  intro y hy
  exact Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    simpa using this

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev topS (Rg : Type) [CommRing Rg] : Over (Sp Rg) := overRes (T := baseOver (Sp Rg)) ⊤

def coord {X : Scheme.{0}} {N : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (n : Fin N) : Γ(X, ⊤) :=
  g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.X n))

def matOf {X : Scheme.{0}} {mA mB : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Fin mA → Fin mB → Γ(X, ⊤) :=
  fun i j => coord g (finProdFinEquiv (i, j))

abbrev affπ (Rg : Type) [CommRing Rg] (N : ℕ) : Sp (MvPolynomial (Fin N) Rg) ⟶ Sp Rg :=
  Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))

variable (A B L M) in

def IsTest {T : Scheme.{0}} (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') : Prop :=
  IsGrpPullback A' A t φA' ∧ IsGrpPullback B' B t φB' ∧ IsMonHom Φ' ∧
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left)

def IsPullD {T₁ T₂ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left)
    (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left)
    (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (h : T₂ ⟶ T₁) : Prop :=
  ∃ (ψA : A₂.left ⟶ A₁.left) (ψB : B₂.left ⟶ B₁.left), IsGrpPullback A₂ A₁ h ψA ∧
    IsGrpPullback B₂ B₁ h ψB ∧ ψA ≫ φA₁ = φA₂ ∧ ψB ≫ φB₁ = φB₂ ∧ Φ₂.left ≫ ψB = ψA ≫ Φ₁.left

variable (A L) in

def IsBCBasis (k : ℕ) {m : ℕ} (b : Fin m → LB.Sec (LPow A L (k : ℤ) (topS Rg))) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (topS Rg).left)
    (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))),
    (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) →
    LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧
    Submodule.span Γ((baseAt t).left, ⊤)
      (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev isoLB (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)} (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) : LB A'.left :=
  LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
    (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))

abbrev zeroPt {R : Type} [CommRing R] (A' : Over (Sp R)) [GrpObj A'] : Sp R ⟶ A'.left := η[A'].left

variable (L M) in

def IsMat (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A']
    [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) : Prop :=
  ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)),
    ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ α.IsGen ∧
    (∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k) ∧
    ∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

variable (L M) in

def Hyps (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) : Prop :=
  IsAbelianScheme A ∧ IsAbelianScheme B ∧ L.IsLB ∧ M.IsLB ∧ eA.IsGen ∧ eB.IsGen ∧ RelAmple A L ∧ 1 ≤ k ∧
    VeryAmpleAt B M k ∧ IsBCBasis A L k bA ∧ IsBCBasis B M k bB

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat
variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]

theorem IsPullD.comp {T₁ T₂ T₃ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] {φA₁ : A₁.left ⟶ A.left}
    {φB₁ : B₁.left ⟶ B.left} {Φ₁ : A₁ ⟶ B₁} {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] {φA₂ : A₂.left ⟶ A.left}
    {φB₂ : B₂.left ⟶ B.left} {Φ₂ : A₂ ⟶ B₂} {A₃ B₃ : Over T₃} [GrpObj A₃] [GrpObj B₃] {φA₃ : A₃.left ⟶ A.left}
    {φB₃ : B₃.left ⟶ B.left} {Φ₃ : A₃ ⟶ B₃} {h₁ : T₂ ⟶ T₁} {h₂ : T₃ ⟶ T₂}
    (p₁ : IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h₁) (p₂ : IsPullD φA₂ φB₂ Φ₂ φA₃ φB₃ Φ₃ h₂) :
    IsPullD φA₁ φB₁ Φ₁ φA₃ φB₃ Φ₃ (h₂ ≫ h₁) := by
  obtain ⟨ψA, ψB, qA, qB, eA, eB, eΦ⟩ := p₁
  obtain ⟨ψA', ψB', qA', qB', eA', eB', eΦ'⟩ := p₂
  refine ⟨ψA' ≫ ψA, ψB' ≫ ψB, qA'.comp qA, qB'.comp qB, by rw [Category.assoc, eA, eA'],
    by rw [Category.assoc, eB, eB'], ?_⟩
  rw [← Category.assoc, eΦ', Category.assoc, eΦ, Category.assoc]

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem hom_ext_affine (Rg : Type) [CommRing Rg] (N : ℕ) (X : Scheme.{0}) (g g' : X ⟶ Sp (MvPolynomial (Fin N) Rg))
    (h0 : g ≫ affπ Rg N = g' ≫ affπ Rg N) (h1 : ∀ n, coord g n = coord g' n) : g = g' := by
  apply ext_of_isAffine
  refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))) _ _).1 ?_
  ext1
  apply MvPolynomial.ringHom_ext
  · intro r
    have e := congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)) h0
    simp only [Scheme.Hom.comp_appTop] at e
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg N).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp]
    rw [n2]
    simpa using e
  · intro n
    exact h1 n

end GlobalTheory.HomFixMat
end
end

