import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0009
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0012
import Development.EtaleCohomology.EtaleSheaves.Bundle0005

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SheafConnectedOfLevelwiseConnected
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

section SlopeTestRemainingChoices
variable {R : Type} [CommRing R]

private theorem cpull_comp' {A B C : Cx R} (f : A ⟶ B) (g : B ⟶ C) (I : Cx R) (n : ℤ)
    (x : CohomologyClass C I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem cpull_id' {A : Cx R} (I : Cx R) (n : ℤ) (x : CohomologyClass A I n) :
    cpull (𝟙 A) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem cpull_homotopy {A B : Cx R} {f g : A ⟶ B} (h : Homotopy f g) (I : Cx R) (n : ℤ)
    (x : CohomologyClass B I n) : cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  rw [cpre_mk, cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • z.comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp z x.1 _ 0 (n + 1) n (by omega) (by omega) rfl]
  simp [zcomp, smul_smul, hz, Cochain.add_comp]

private theorem cpull_bij {A B : Cx R} (e : HomotopyEquiv A B) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp', cpull_homotopy e.homotopyInvHomId, cpull_id']
  · rw [← cpull_comp', cpull_homotopy e.homotopyHomInvId, cpull_id']

private theorem transfer {A B A' B' : Cx R} (g : A ⟶ B) (g' : A' ⟶ B') (a : HomotopyEquiv A A')
    (b : HomotopyEquiv B B') (w : g ≫ b.hom = a.hom ≫ g') (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull g' I n) → Function.Bijective (cpull g I n)) ∧
      (Function.Injective (cpull g' I n) → Function.Injective (cpull g I n)) := by
  have ha := cpull_bij a I n
  have hb := cpull_bij b I n
  have key : ⇑(cpull g I n) = cpull a.hom I n ∘ cpull g' I n ∘ (Equiv.ofBijective _ hb).symm := by
    funext x
    obtain ⟨y, rfl⟩ := hb.2 x
    have : (Equiv.ofBijective _ hb).symm (cpull b.hom I n y) = y :=
      (Equiv.ofBijective _ hb).symm_apply_apply y
    simp only [Function.comp_apply, this]
    rw [← cpull_comp', ← cpull_comp', w]
  rw [key]
  exact ⟨fun h => ha.comp (h.comp (Equiv.bijective _)),
    fun h => ha.1.comp (h.comp (Equiv.injective _))⟩

private theorem subsingleton_of_isZero {A : Cx R} (h : IsZero A) (I : Cx R) (n : ℤ) :
    Subsingleton (CohomologyClass A I n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_))
  exact ((HomologicalComplex.eval _ _ p).map_isZero h).eq_of_src _ _

private theorem bij_of_isZero {A B : Cx R} (hA : IsZero A) (hB : IsZero B) (g : A ⟶ B) (I : Cx R)
    (n : ℤ) : Function.Bijective (cpull g I n) := by
  have := subsingleton_of_isZero hA I n
  have := subsingleton_of_isZero hB I n
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem core (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ)
    (e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)))
    (he : ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
      (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom)
    (h : ∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) :
    UpperTheory.RedSh.Conn p F m := by
  obtain ⟨-, hinj, hge, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  have := hle E
  have := hle E'
  refine UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective R (res R F) hinj ((chains R).map p) m fun q => ?_
  rcases lt_or_ge 0 q with hq | hq
  · have hz : ∀ K : Cx R, K.IsStrictlyLE 0 →
        IsZero ((CochainComplex.singleFunctor (Shv R) 0).obj (K.X q)) := fun K _ =>
      (CochainComplex.singleFunctor (Shv R) 0).map_isZero (K.isZero_of_isStrictlyLE 0 q hq)
    exact ⟨fun n _ => bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _,
      (bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _).1⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = -(k : ℤ) := ⟨(-q).toNat, by omega⟩
    let S := CochainComplex.singleFunctor (Shv R) 0
    let φ := p.app (op (SimplexCategory.mk k))
    let a : HomotopyEquiv (S.obj (((chains R).obj E').X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E' k))).trans (e _)
    let b : HomotopyEquiv (S.obj (((chains R).obj E).X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E k))).trans (e _)
    have w : S.map (((chains R).map p).f (-(k : ℤ))) ≫ b.hom =
        a.hom ≫ (chains R).map (disc.map φ) := by
      change S.map _ ≫ S.map (chainsXIso R E k).hom ≫ (e _).hom =
        (S.map (chainsXIso R E' k).hom ≫ (e _).hom) ≫ _
      rw [Category.assoc, he, ← Category.assoc, ← S.map_comp, hnat, S.map_comp, Category.assoc]
    have hm : m + -(k : ℤ) = m - k := by ring
    rw [hm]
    refine ⟨fun n hn => (transfer _ _ a b w _ n).1 ((h k).1 n hn),
      (transfer _ _ a b w _ _).2 (h k).2⟩

end SlopeTestRemainingChoices

theorem UpperTheory.sheafConnected_of_levelwise_connected :
    ∀ (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ), (∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) → UpperTheory.RedSh.Conn p F m := by
  intro R _ F E' E p m h
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact core R F p m e he h
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SpecializationTensorRingHomProperties
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

section
variable {k L A : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]

private lemma map_val_injective (R : Subalgebra k L) :
    Function.Injective
      (Algebra.TensorProduct.map R.val (AlgHom.id k A) : R ⊗[k] A →ₐ[k] L ⊗[k] A) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := A)
    (R.val.toLinearMap) Subtype.val_injective
  have e : ∀ z : R ⊗[k] A, LinearMap.rTensor A R.val.toLinearMap z =
      Algebra.TensorProduct.map R.val (AlgHom.id k A) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply h
  rw [e, e, hxy]

private lemma spz_add {R : Subalgebra k L} {φ : R →ₐ[k] k} {y y' : L ⊗[k] A} {a a' : A}
    (h : Spz R φ y a) (h' : Spz R φ y' a') : Spz R φ (y + y') (a + a') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨v, hv, rfl⟩ := h'
  exact ⟨u + v, by rw [map_add, hu, hv], by simp only [map_add]⟩

private lemma spz_tmul (R : Subalgebra k L) (φ : R →ₐ[k] k) (r : R) (a : A) :
    Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a) :=
  ⟨r ⊗ₜ[k] a, by simp, by simp⟩

private noncomputable def contr (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] :
    B ⊗[k] A →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ LinearMap.lTensor B l

private lemma contr_tmul (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] (b : B) (a : A) :
    contr l B (b ⊗ₜ[k] a) = l a • b := by
  simp [contr]

private lemma exists_contr_ne_zero {y : L ⊗[k] A} (hy : y ≠ 0) :
    ∃ l : A →ₗ[k] k, contr l L y ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k A
  let E := TensorProduct.equivFinsuppOfBasisRight (R := k) (M := L) (N := A) b
  have hE : E y ≠ 0 := fun h => hy (E.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hE
  refine ⟨b.coord i, ?_⟩
  have key : ∀ z : L ⊗[k] A, contr (b.coord i) L z = E z i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [contr_tmul, E, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply]
  rw [key]
  simpa using hi
end

theorem UpperTheory.specialization_tensor_ring_hom_properties :
    ∀ (k L A : Type) [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A], (∀ (R : Subalgebra k L) (φ : R →ₐ[k] k), (∀ (y : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y a' → a = a') ∧ (∀ (y y' : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y' a' → Spz R φ (y + y') (a + a') ∧ Spz R φ (y * y') (a * a') ∧ Spz R φ (y - y') (a - a')) ∧ (∀ (r : R) (a : A), Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a)) ∧ ∀ (A' : Type) [CommRing A'] [Algebra k A'] (g : A →ₐ[k] A') (y : L ⊗[k] A) (a : A), Spz R φ y a → Spz R φ (Algebra.TensorProduct.map (AlgHom.id k L) g y) (g a)) ∧ (∀ y : L ⊗[k] A, ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ φ : R →ₐ[k] k, ∃ a, Spz R φ y a) ∧ ∀ y : L ⊗[k] A, y ≠ 0 → ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ (φ : R →ₐ[k] k) (a : A), Spz R φ y a → a ≠ 0 := by
  intro k L A _ _ _ _ _
  refine ⟨fun R φ => ⟨?_, ?_, spz_tmul R φ, ?_⟩, ?_, ?_⟩
  · rintro y a a' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [map_val_injective R (hu.trans hv.symm)]
  · intro y y' a a' h h'
    refine ⟨spz_add h h', ?_, ?_⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u * v, by rw [map_mul, hu, hv], by simp only [map_mul]⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u - v, by rw [map_sub, hu, hv], by simp only [map_sub]⟩
  · rintro A' _ _ g y a ⟨u, rfl, rfl⟩
    refine ⟨Algebra.TensorProduct.map (AlgHom.id k R) g u, ?_, ?_⟩
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
  · intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact ⟨∅, fun R _ φ => ⟨0, 0, by simp, by simp⟩⟩
    | tmul l b =>
      classical
      refine ⟨{l}, fun R hs φ => ?_⟩
      have hl : l ∈ R := hs (by simp)
      exact ⟨_, spz_tmul R φ ⟨l, hl⟩ b⟩
    | add x y hx hy =>
      classical
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      refine ⟨s ∪ t, fun R hst φ => ?_⟩
      obtain ⟨a, ha⟩ := hs R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      obtain ⟨b, hb⟩ := ht R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      exact ⟨a + b, spz_add ha hb⟩
  · intro y hy
    classical
    obtain ⟨l, hl⟩ := exists_contr_ne_zero hy
    set c := contr l L y with hc
    refine ⟨{c, c⁻¹}, fun R hs φ a ha h0 => ?_⟩
    have hcR : c ∈ R := hs (by simp)
    have hcR' : c⁻¹ ∈ R := hs (by simp)
    obtain ⟨u, hu, hua⟩ := ha
    have e1 : ∀ z : R ⊗[k] A, ((contr l R z : R) : L) =
        contr l L (Algebra.TensorProduct.map R.val (AlgHom.id k A) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul]
      | add x y hx hy => simp only [map_add, hx, hy, Subalgebra.coe_add]
    have e2 : ∀ z : R ⊗[k] A, φ (contr l R z) =
        l (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map φ (AlgHom.id k A) z)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul, mul_comm]
      | add x y hx hy => simp only [map_add, hx, hy]
    have h1 : contr l R u = ⟨c, hcR⟩ := Subtype.ext (by rw [e1, hu])
    have h2 : φ ⟨c, hcR⟩ = 0 := by rw [← h1, e2, hua, h0, map_zero]
    have h3 : (⟨c, hcR⟩ : R) * ⟨c⁻¹, hcR'⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hl)
    have h4 := congrArg φ h3
    rw [map_mul, h2, zero_mul, map_one] at h4
    exact zero_ne_one h4
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.PbSp

private theorem hom_val {c : Act} {A : CommRingCat.{0}} {J : Type} [SmallCategory J] {F G : J ⥤ Ob c A} (h : F = G)
    {i j : J} (f : i ⟶ j) : (F.map f).1 = (G.map f).1 := by
  subst h
  rfl

private theorem law_id {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    (j : J) : φ.g.app A 1 = (x.map (𝟙 j)).1 := by
  rw [x.map_id]
  exact map_one _

private theorem law_comp {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (p q : P.G.obj A) (hp : φ.g.app A p = (x.map f).1)
    (hq : φ.g.app A q = (x.map g).1) : φ.g.app A (p * q) = (x.map (f ≫ g)).1 := by
  rw [x.map_comp]
  change _ = (x.map f).1 * (x.map g).1
  rw [map_mul, hp, hq]

private theorem fn_square {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h1 : ∀ z : P.D.obj A, r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z))
    (h2 : ∀ z : P.G.obj A, r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) :
    t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := by
  have ho : ∀ z : Ob P A, (t.fn A ⋙ r.fn A).obj z = (l.fn A ⋙ u.fn A).obj z :=
    fun z => congrArg Ob.mk (h1 z.pt)
  refine Functor.hext ho (fun z w f => ?_)
  exact Ob.hom_heq (ho z) (ho w) _ _ (h2 f.1)

private theorem lift_chain {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h3 : ∀ (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y)
    (h4 : ∀ (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h)
    {J : Type} [SmallCategory J] (x : J ⥤ Ob a A) (y : J ⥤ Ob b A) (h : x ⋙ r.fn A = y ⋙ u.fn A) :
    ∃! z : J ⥤ Ob P A, z ⋙ t.fn A = x ∧ z ⋙ l.fn A = y := by
  have hobj : ∀ j, r.d.app A (x.obj j).pt = u.d.app A (y.obj j).pt :=
    fun j => congrArg (fun F : J ⥤ Ob c A => (F.obj j).pt) h
  have hmap : ∀ (i j : J) (f : i ⟶ j), r.g.app A (x.map f).1 = u.g.app A (y.map f).1 :=
    fun i j f => hom_val h f
  choose zo hzo hzu using fun j => h3 (x.obj j).pt (y.obj j).pt (hobj j)
  choose zg hzg hzgu using fun (i j : J) (f : i ⟶ j) => h4 (x.map f).1 (y.map f).1 (hmap i j f)
  let F : J ⥤ Ob P A :=
    { obj := fun j => Ob.mk (zo j)
      map := fun {i j} f => ⟨zg i j f, by
        refine (hzu i _ ⟨?_, ?_⟩).symm
        · change t.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [t.eq, (hzg i j f).1, (hzo j).1]
          exact (x.map f).2.symm
        · change l.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [l.eq, (hzg i j f).2, (hzo j).2]
          exact (y.map f).2.symm⟩
      map_id := fun j => by
        apply Subtype.ext
        exact (hzgu j j (𝟙 j) 1 ⟨law_id t x j, law_id l y j⟩).symm
      map_comp := fun {i j k} f g => by
        apply Subtype.ext
        exact (hzgu i k (f ≫ g) (zg i j f * zg j k g)
          ⟨law_comp t x f g _ _ (hzg i j f).1 (hzg j k g).1,
            law_comp l y f g _ _ (hzg i j f).2 (hzg j k g).2⟩).symm }
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · have ho : ∀ j, (F ⋙ t.fn A).obj j = x.obj j := fun j => congrArg Ob.mk (hzo j).1
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).1)
  · have ho : ∀ j, (F ⋙ l.fn A).obj j = y.obj j := fun j => congrArg Ob.mk (hzo j).2
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).2)
  · rintro w ⟨hw1, hw2⟩
    have ho : ∀ j, w.obj j = F.obj j := fun j =>
      congrArg Ob.mk (hzu j (w.obj j).pt
        ⟨congrArg (fun G : J ⥤ Ob a A => (G.obj j).pt) hw1,
          congrArg (fun G : J ⥤ Ob b A => (G.obj j).pt) hw2⟩)
    exact Functor.hext ho (fun i j f =>
      Ob.hom_heq (ho i) (ho j) _ _ (hzgu i j f (w.map f).1 ⟨hom_val hw1 f, hom_val hw2 f⟩))

private abbrev Ch (a : Act) (k : ℕ) (T : Scheme.{0}) : Type := Fin (k + 1) ⥤ Ob a (Scheme.Γ.obj (op T))

private def pr1 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Sx E k T :=
  Prod.fst (α := Sx E k T) (β := Ch a k T) s

private def pr2 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Ch a k T :=
  Prod.snd (α := Sx E k T) (β := Ch a k T) s

private def mkS {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (e : Sx E k T) (x : Ch a k T) : Sx (Sp E a) k T :=
  Prod.mk (α := Sx E k T) (β := Ch a k T) e x

end UpperTheory.PbSp

open UpperTheory.PbSp in
theorem UpperTheory.stackProduct_isPullback_of_actionPullback :
    ∀ (E : Spc) {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c),
        (∀ A (z : P.D.obj A), r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z)) →
        (∀ A (z : P.G.obj A), r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) →
        (∀ A (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y) →
        (∀ A (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h) →
        IsPullback (Sp.map E t) (Sp.map E l) (Sp.map E r) (Sp.map E u) := by
  intro E P a b c t l r u h1 h2 h3 h4
  have hsq : ∀ A, t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := fun A => fn_square t l r u A (h1 A) (h2 A)
  apply isPullback_of_unique_simplices_pullback
  · ext k T s
    refine Prod.ext rfl ?_
    exact congrArg (fun F => s.2 ⋙ F) (hsq _)
  · intro k T x y hxy
    have e1 : pr1 x = pr1 y := congrArg pr1 hxy
    have e2 : pr2 x ⋙ r.fn _ = pr2 y ⋙ u.fn _ := congrArg pr2 hxy
    obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ := lift_chain t l r u _ (h3 _) (h4 _) (pr2 x) (pr2 y) e2
    refine ⟨mkS (pr1 x) z, ⟨?_, ?_⟩, ?_⟩
    · change mkS (pr1 x) (z ⋙ t.fn _) = x
      rw [hz1]
      rfl
    · change mkS (pr1 x) (z ⋙ l.fn _) = y
      rw [hz2, e1]
      rfl
    · rintro w ⟨hw1, hw2⟩
      have f1 : pr1 w = pr1 x := congrArg pr1 hw1
      have f2 : pr2 w = z := hzu _ ⟨congrArg pr2 hw1, congrArg pr2 hw2⟩
      change mkS (pr1 w) (pr2 w) = mkS (pr1 x) z
      rw [f1, f2]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TensorFractionRingExistsMulEqOfDenominator
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator :
    ∀ (k L K : Type) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] (B : Subalgebra k K), IsFractionRing B K → ∀ t : L ⊗[k] K, ∃ (s : L ⊗[k] B) (β : B), β ≠ 0 ∧ t * ((1 : L) ⊗ₜ[k] (β : K)) = inc L B s := by
  intro k L K _ _ _ _ _ B hB t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul l κ =>
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) κ
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (b : K) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
    refine ⟨l ⊗ₜ[k] a, b, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    congr 1
    rw [← hab]
    change (a : K) / (b : K) * b = a
    field_simp
  | add x y hx hy =>
    obtain ⟨s1, β1, h1, e1⟩ := hx
    obtain ⟨s2, β2, h2, e2⟩ := hy
    refine ⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩
    have i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K) := by simp [inc]
    have i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K) := by simp [inc]
    have split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) =
        ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]
    rw [map_add, map_mul, map_mul, i1, i2, ← e1, ← e2, split]
    ring
end

