import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0333
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0345

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheaf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscChains

def heExt {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] {K L : ChainComplex C ℕ}
    (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

variable (R : Type) [CommRing R]

def heN (P : PSh) :
    HomotopyEquiv ((chainsN R).obj (disc.obj P)) ((ChainComplex.single₀ (Shv R)).obj ((free R).obj P)) :=
  (HomotopyEquiv.ofIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).mapIso
      (Functor.constComp _ P (free R)))).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const ((free R).obj P)).homotopyEquiv

lemma heN_inv_f_zero (P : PSh) :
    (heN R P).inv.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom := by
  dsimp [heN, HomotopyEquiv.trans, HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
  erw [HomologicalComplex.comp_f]
  erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  simp
  exact Category.comp_id _

def he (P : PSh) : HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)) :=
  (HomotopyEquiv.ofIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat ((free R).obj P) 0 0
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).symm).trans
    (heExt (heN R P)).symm

lemma he_hom_f_zero (P : PSh) : sglι _ ≫ (he R P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv := by
  dsimp [he, heExt, HomotopyEquiv.trans, HomotopyEquiv.symm, HomotopyEquiv.ofIso]
  erw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl), heN_inv_f_zero]
  rw [sglι, chainsXIso]
  erw [Category.assoc, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.DiscChains

namespace GlobalTheory.EtC

theorem chains_disc_homotopyEquiv : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  intro R _
  refine ⟨DiscChains.he R, DiscChains.he_hom_f_zero R, fun {P Q} f => ?_⟩
  obtain ⟨-, hnat, -⟩ := GlobalTheory.EtC.chains_basic R
  apply HomologicalComplex.from_single_hom_ext
  apply (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((free R).obj P)) _ _).1
  change sglι _ ≫ _ = sglι _ ≫ _
  have e1 : ((DiscChains.he R P).hom ≫ (chains R).map (disc.map f)).f 0 =
      (DiscChains.he R P).hom.f 0 ≫ ((chains R).map (disc.map f)).f 0 := HomologicalComplex.comp_f _ _ _
  have e2 : ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (DiscChains.he R Q).hom).f 0 =
      ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 ≫ (DiscChains.he R Q).hom.f 0 :=
    HomologicalComplex.comp_f _ _ _
  rw [e1, e2, ← Category.assoc, DiscChains.he_hom_f_zero]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 =
      (free R).map f ≫ sglι ((free R).obj Q) := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h1, Category.assoc, DiscChains.he_hom_f_zero]
  rw [← cancel_mono (chainsXIso R (disc.obj Q) 0).hom]
  have h2 := hnat (disc.map f) 0
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [h2]
  simp

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdeals
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.FinInterNil

theorem exists_ne_zero_isNilpotent_mul {D E : Type} [CommRing D] [IsDomain D] [CommRing E]
    [Algebra D E] (y : E)
    (hy : ∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → y ∈ Q) :
    ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) := by
  by_contra hcon
  push_neg at hcon
  let M : Submonoid E :=
    { carrier := {z | ∃ t : D, t ≠ 0 ∧ ∃ n : ℕ, z = algebraMap D E t * y ^ n}
      mul_mem' := by
        rintro a b ⟨t, ht, n, rfl⟩ ⟨t', ht', m, rfl⟩
        exact ⟨t * t', mul_ne_zero ht ht', n + m, by rw [map_mul, pow_add]; ring⟩
      one_mem' := ⟨1, one_ne_zero, 0, by simp⟩ }
  have h0 : (0 : E) ∉ M := by
    rintro ⟨t, ht, n, hz⟩
    apply hcon t ht
    refine ⟨n + 1, ?_⟩
    calc (algebraMap D E t * y) ^ (n + 1)
        = algebraMap D E t ^ n * y * (algebraMap D E t * y ^ n) := by ring
      _ = 0 := by rw [← hz, mul_zero]
  have hdisj : Disjoint ((⊥ : Ideal E) : Set E) (M : Set E) := by
    rw [Set.disjoint_left]
    intro z hz hzM
    have hz0 : z = 0 := by simpa using hz
    exact h0 (hz0 ▸ hzM)
  obtain ⟨Q, hQ, -, hQM⟩ := Ideal.exists_le_prime_disjoint ⊥ M hdisj
  have hcomap : Q.comap (algebraMap D E) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Ideal.mem_bot]
    by_contra htne
    have hm : algebraMap D E t ∈ M := ⟨t, htne, 0, by simp⟩
    exact Set.disjoint_left.mp hQM (Ideal.mem_comap.mp ht) hm
  have hyQ := hy Q hQ hcomap
  have hm : y ∈ M := ⟨1, one_ne_zero, 1, by simp⟩
  exact Set.disjoint_left.mp hQM hyQ hm

theorem main : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type)
    (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) →
    (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) →
    ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  intro D E _ _ _ _ ι X P hFG hQ
  classical
  have hstep : ∀ y ∈ (⨅ i ∈ X, P i), ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) :=
    fun y hy => exists_ne_zero_isNilpotent_mul y (fun Q hQp hQc => hQ Q hQp hQc hy)
  have hJfg : (∏ i ∈ X, P i).FG := by
    refine Finset.prod_induction P (fun J : Ideal E => J.FG) (fun a b ha hb => ha.mul hb) ?_ hFG
    exact ⟨{1}, by simp⟩
  have hJI : ∀ g ∈ ∏ i ∈ X, P i, g ∈ (⨅ i ∈ X, P i) := by
    intro g hg
    simp only [Submodule.mem_iInf]
    intro i hi
    exact (Ideal.prod_le_inf.trans (Finset.inf_le hi)) hg
  obtain ⟨S, hS⟩ := hJfg
  have hSI : ∀ g : S, (g : E) ∈ (⨅ i ∈ X, P i) := fun g =>
    hJI g (hS ▸ Submodule.subset_span g.2)
  choose t ht using fun g : S => hstep g.1 (hSI g)
  refine ⟨∏ g : S, t g, Finset.prod_ne_zero_iff.mpr (fun g _ => (ht g).1), ?_⟩
  set s := ∏ g : S, t g with hs
  let K : Ideal E := Submodule.comap (LinearMap.mulLeft E (algebraMap D E s)) (nilradical E)
  have hK : ∀ z, z ∈ K ↔ IsNilpotent (algebraMap D E s * z) := by
    intro z
    simp [K, mem_nilradical]
  have hJK : (∏ i ∈ X, P i) ≤ K := by
    rw [← hS, Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, hK]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ (⟨g, hg⟩ : S))
    have he : algebraMap D E s * g = algebraMap D E c * (algebraMap D E (t ⟨g, hg⟩) * g) := by
      rw [hs, hc, map_mul]; ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left (ht ⟨g, hg⟩).2
  intro y hy
  have hyN : y ^ X.card ∈ ∏ i ∈ X, P i := by
    have := Ideal.prod_mem_prod (s := X) (I := P) (x := fun _ => y) (fun i hi => by
      have := hy
      simp only [Submodule.mem_iInf] at this
      exact this i hi)
    simpa [Finset.prod_const] using this
  have hn := (hK _).mp (hJK hyN)
  have hpow : IsNilpotent ((algebraMap D E s * y) ^ (X.card + 1)) := by
    have he : (algebraMap D E s * y) ^ (X.card + 1)
        = (algebraMap D E s ^ X.card * y) * (algebraMap D E s * y ^ X.card) := by ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left hn
  obtain ⟨k, hk⟩ := hpow
  exact ⟨(X.card + 1) * k, by rw [pow_mul, hk]⟩

end GlobalTheory.FinInterNil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubring
section
open Polynomial

namespace GlobalTheory

theorem finiteDimensional_top_subfield (L : Type*) [Field L] :
    FiniteDimensional (⊤ : Subfield L) L := by
  refine ⟨⟨{1}, eq_top_iff.mpr fun l _ => ?_⟩⟩
  rw [Finset.coe_singleton, Submodule.mem_span_singleton]
  exact ⟨⟨l, Subfield.mem_top l⟩, mul_one l⟩

theorem exists_normal_finiteType_subring_of_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  intro K L _ _ φ c hfin V hc t ht hgen
  classical
  letI : Algebra ℂ K := c.toAlgebra
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra ℂ L := (φ.comp c).toAlgebra
  haveI : IsScalarTower ℂ K L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have ht' : ∀ x : t, ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 :=
    fun x => (ht x x.2).2
  choose p hpm hpc hpx using ht'
  let T : Set K := ⋃ x : t, ((p x).coeffs : Set K)
  have hT : T.Finite := Set.finite_iUnion fun x => (p x).coeffs.finite_toSet
  let A : Subalgebra ℂ K := Algebra.adjoin ℂ T
  haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite hT
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcoefA : ∀ x : t, ∀ n, (p x).coeff n ∈ A := fun x n => by
    by_cases h : (p x).coeff n = 0
    · rw [h]; exact A.zero_mem
    · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨x, Polynomial.coeff_mem_coeffs h⟩)
  have hAE : ∀ y ∈ A, y ∈ V.comap φ := fun y hy => by
    let E' : Subalgebra ℂ K := { (V.comap φ).toSubring with algebraMap_mem' := fun a => hc a }
    have : A ≤ E' := Algebra.adjoin_le (by
      intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hpc x i)
    exact this hy
  haveI : IsScalarTower A K L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ A L := .of_algebraMap_eq fun _ => rfl
  have hint : ∀ x : t, IsIntegral A (x : L) := fun x => by
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap A K)
      ((lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, hcoefA x n⟩, rfl⟩) (hpm x)
    refine ⟨q, hqm, ?_⟩
    rw [← hpx x, ← hq, eval₂_map]
    rfl

  have hsub : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤ (integralClosure A L).toSubring :=
    Subring.closure_le.mpr (Set.union_subset
      (by
        rintro _ ⟨a, rfl⟩
        exact isIntegral_algebraMap (R := A) (x := (⟨c a, A.algebraMap_mem a⟩ : A)))
      (fun x hx => hint ⟨x, hx⟩))
  have hall : ∀ l : L, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)),
      ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)), (l = b / d ∨ l⁻¹ = b / d) := by
    intro l
    rcases V.mem_or_inv_mem l with h | h
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen l h
      exact ⟨b, hb, d, hd, Or.inl he⟩
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen _ h
      exact ⟨b, hb, d, hd, Or.inr he⟩
  haveI : Algebra.IsAlgebraic A L := ⟨fun l => by
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hb' : IsAlgebraic A b := (hsub hb : IsIntegral A b).isAlgebraic
    have hd' : IsAlgebraic A d := (hsub hd : IsIntegral A d).isAlgebraic
    have hbd : IsAlgebraic A (b / d) := by rw [div_eq_mul_inv]; exact hb'.mul hd'.inv
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact hbd.inv⟩
  haveI : Algebra.IsAlgebraic A K := ⟨fun k =>
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A K L) φ.injective).mp
      (Algebra.IsAlgebraic.isAlgebraic (φ k))⟩
  have htop : Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L)) = ⊤ := by
    refine eq_top_iff.mpr fun l _ => ?_
    have hle : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤
        (Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L))).toSubring :=
      Subring.closure_le.mpr Subfield.subset_closure
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hbd := Subfield.div_mem _ (hle hb) (hle hd)
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact Subfield.inv_mem _ hbd
  haveI : Algebra.EssFiniteType ℂ L := by
    refine essFiniteType_of_finiteDimensional_subfield_closure t.finite_toSet ?_
    rw [htop]
    exact finiteDimensional_top_subfield L
  haveI : Algebra.EssFiniteType A L := .of_comp ℂ A L
  haveI := finite_integralClosure_of_essFiniteType_field ℂ A L
  let S := integralClosure A K
  let f : S →ₐ[A] integralClosure A L :=
    ((IsScalarTower.toAlgHom A K L).comp S.val).codRestrict _ fun z =>
      (z.2.map (IsScalarTower.toAlgHom A K L) : IsIntegral A _)
  haveI : Module.Finite A S := Module.Finite.of_injective f.toLinearMap fun z w h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h : _))
  haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  haveI : IsFractionRing S K := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
  haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff K).mpr fun {x} hx =>
    ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

  have hcR : ∀ a, c a ∈ S.toSubring := fun a => S.algebraMap_mem (⟨c a, A.algebraMap_mem a⟩ : A)
  refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
  · intro x hx
    obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
    let ι : A →+* V.comap φ :=
      { toFun := fun a => ⟨a, hAE a a.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hE : IsIntegral (V.comap φ) x := by
      refine ⟨q.map ι, hqm.map ι, ?_⟩
      rw [eval₂_map]
      exact hq
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
    exact y.2
  · exact (inferInstance : IsNoetherianRing S)
  · exact (inferInstance : IsIntegrallyClosed S)
  · exact (inferInstance : IsFractionRing S K)
  · intro x hx
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := S.toSubring.subtype)
      ((lifts_iff_coeff_lifts _).mpr fun n =>
        ⟨⟨_, S.algebraMap_mem (⟨_, hcoefA ⟨x, hx⟩ n⟩ : A)⟩, rfl⟩) (hpm ⟨x, hx⟩)
    refine ⟨q, hqm, ?_⟩
    rw [← eval₂_map, hq]
    exact hpx ⟨x, hx⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalExtensionWithSimpleRootStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_local_extension_with_simple_root : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω] (u : A →+* Ω) (p : Polynomial A) (α : Ω), RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic → (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω), a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  first | exact @GlobalTheory.MonicRootExtension.exists_extension | exact GlobalTheory.MonicRootExtension.exists_extension | (intros; apply GlobalTheory.MonicRootExtension.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRoots
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

theorem mem_range_of_AIC_of_eval₂_eq_zero {T L : Type} [CommRing T] [CommRing L] [IsDomain L]
    (hA : AIC T) (f : T →+* L) (x : L) :
    ∀ (n : ℕ) (p : T[X]), p.natDegree = n → p.Monic → p.eval₂ f x = 0 → x ∈ Set.range f := by
  intro n
  haveI : Nontrivial T := f.domain_nontrivial
  induction n with
  | zero =>
    intro p hd hm hx
    have hp : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst hp
    simp at hx
  | succ n ih =>
    intro p hd hm hx
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hroot : IsRoot p a := ha
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hXm : (X - C a : T[X]).Monic := Polynomial.monic_X_sub_C a
    have hqm : q.Monic := by
      exact Polynomial.Monic.of_mul_monic_left hXm (by rw [hfac]; exact hm)
    have hqd : q.natDegree = n := by
      have h1 : ((X - C a) * q).natDegree = (X - C a).natDegree + q.natDegree :=
        hXm.natDegree_mul hqm
      rw [hfac, hd, Polynomial.natDegree_X_sub_C] at h1
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨a, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
      exact (sub_eq_zero.mp h).symm
    · exact ih q hqd hqm h

theorem exists_retraction_of_AIC : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T]
    [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E],
    AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ →
    ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  intro D T E _ _ _ _ _ _ _ _ _ hA ι Q hQ hQD
  let π : E →ₐ[D] E ⧸ Q := Ideal.Quotient.mkₐ D Q
  let f : T →ₐ[D] E ⧸ Q := π.comp ι

  have hker : RingHom.ker (f : T →+* E ⧸ Q) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := D)
    rw [← hQD]
    ext d
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change f (algebraMap D T d) = 0 ↔ _
    rw [f.commutes]
    change algebraMap D (E ⧸ Q) d = 0 ↔ _
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ Q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective f := by
    have := (RingHom.injective_iff_ker_eq_bot (f : T →+* E ⧸ Q)).mpr hker
    exact this

  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hpe⟩ := (Algebra.IsIntegral.isIntegral (R := D) e)
    have hmem := mem_range_of_AIC_of_eval₂_eq_zero hA (f : T →+* E ⧸ Q) (Ideal.Quotient.mk Q e)
      _ (p.map (algebraMap D T)) rfl (hpm.map _) (by
        rw [Polynomial.eval₂_map]
        have hc : (f : T →+* E ⧸ Q).comp (algebraMap D T) = (Ideal.Quotient.mk Q).comp (algebraMap D E) := by
          ext d
          simp only [RingHom.comp_apply, RingHom.coe_coe]
          rw [f.commutes]
          rfl
        rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero])
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht⟩
  let eqv : T ≃ₐ[D] E ⧸ Q := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨(eqv.symm : E ⧸ Q →ₐ[D] T).comp π, ?_, ?_⟩
  · ext t
    simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_coe]
    apply eqv.injective
    change eqv (eqv.symm (π (ι t))) = eqv t
    rw [AlgEquiv.apply_symm_apply]
    rfl
  · ext e
    rw [RingHom.mem_ker]
    change eqv.symm (π e) = 0 ↔ e ∈ Q
    rw [AlgEquiv.symm_apply_eq, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLimitOfDoublingJets
section
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem limit_of_jets (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A)
    (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (φ : ℕ → A → PowerSeries R)
    (hφ : ∀ n, IsJet π ε m β δ (n + 2) (φ n))
    (hc : ∀ n f, (X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) :
    ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧
      PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧
      (PowerSeries.rescale 2).comp γ = γ.comp m := by

  have hdv : ∀ (n : ℕ) (p q : PowerSeries R), (X : PowerSeries R) ^ n ∣ p - q →
      ∀ k, k < n → coeff k p = coeff k q := by
    intro n p q h k hk
    have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
    rwa [map_sub, sub_eq_zero] at this

  have hstab : ∀ f k j, k ≤ j + 1 → coeff k (φ j f) = coeff k (φ k f) := by
    intro f k j hkj
    rcases Nat.lt_or_ge j k with h | h
    · have hk : k = j + 1 := by omega
      subst hk
      exact (hdv _ _ _ (hc j f) (j + 1) (by omega)).symm
    · induction j, h using Nat.le_induction with
      | base => rfl
      | succ j hj ih =>
        rw [hdv _ _ _ (hc j f) k (by omega)]
        exact ih (by omega)
  let g : A → PowerSeries R := fun f => PowerSeries.mk fun k => coeff k (φ k f)
  have hg : ∀ f k j, k ≤ j + 1 → coeff k (g f) = coeff k (φ j f) := by
    intro f k j hkj
    simp only [g, PowerSeries.coeff_mk]
    exact (hstab f k j hkj).symm
  have gmul : ∀ f h, g (f * h) = g f * g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.1 f h) k (by omega), coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hg f x.1 k (by omega), hg h x.2 k (by omega)]
  have gadd : ∀ f h, g (f + h) = g f + g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.1 f h) k (by omega), map_add, map_add,
      hg f k k (by omega), hg h k k (by omega)]
  have gone : g 1 = 1 := by
    ext k
    rw [hg _ k k (by omega), hdv _ _ _ (hφ k).1.2.2.1 k (by omega)]
  have gzero : g 0 = 0 := by
    have := gadd 0 0
    rw [add_zero] at this
    linear_combination -this
  let γ : A →+* PowerSeries R :=
    { toFun := g, map_one' := gone, map_mul' := gmul, map_zero' := gzero, map_add' := gadd }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · ext b k
    show coeff k (g (π b)) = coeff k (C (β b))
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.2.2 b) k (by omega)]
  · ext f
    show constantCoeff (g f) = β (ε f)
    rw [← coeff_zero_eq_constantCoeff_apply, hg f 0 0 (by omega), coeff_zero_eq_constantCoeff_apply,
      (hφ 0).2.2.1 f]
  · intro f
    show coeff 1 (g f) = δ f
    rw [hg f 1 0 (by omega), (hφ 0).2.2.2 f]
  · ext f k
    show coeff k (rescale 2 (g f)) = coeff k (g (m f))
    rw [coeff_rescale, hg f k k (by omega), hg (m f) k k (by omega),
      hdv _ _ _ ((hφ k).2.1 f) k (by omega), coeff_rescale]

end GlobalTheory.Nef.PathJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDivisionPointNeZeroStatement
section
open Complex Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_division_point_ne_zero : ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | exact GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | (intros; apply GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero <;> assumption)
end

