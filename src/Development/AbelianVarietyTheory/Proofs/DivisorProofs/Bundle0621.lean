import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingHens
section
open IsLocalRing GlobalTheory.Henselisation Polynomial

namespace GlobalTheory.Henselisation

theorem eval_derivative_scaleRoots_mul {S : Type*} [CommRing S] (p : S[X]) (s x : S) :
    (derivative (p.scaleRoots s)).eval (s * x) = s ^ (p.natDegree - 1) * (derivative p).eval x := by
  have h1 : (derivative (p.scaleRoots s)).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le (p.scaleRoots s)
    rw [natDegree_scaleRoots] at this; omega
  have h2 : (derivative p).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le p; omega
  rw [eval_eq_sum_range' h1, eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_derivative, coeff_derivative, coeff_scaleRoots]
  by_cases hkd : k + 1 ≤ p.natDegree
  · have e : s ^ (p.natDegree - (k + 1)) * (s * x) ^ k = s ^ (p.natDegree - 1) * x ^ k := by
      rw [mul_pow, ← mul_assoc, ← pow_add]; congr 2; omega
    calc _ = p.coeff (k + 1) * (↑k + 1) * (s ^ (p.natDegree - (k + 1)) * (s * x) ^ k) := by ring
      _ = _ := by rw [e]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring

theorem isUnit_of_sub_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {x u : S}
    (hu : IsUnit u) (h : x - u ∈ maximalIdeal S) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal S := (mem_maximalIdeal x).2 hx
  have : u ∈ maximalIdeal S := by
    have := Ideal.sub_mem _ hx' h; simpa using this
  exact (mem_maximalIdeal u).1 this hu

theorem henselianLocalRing_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R],
    HenselianLocalRing (Hens R) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  obtain ⟨hloc, hofloc⟩ := GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of R
  letI := hloc
  refine { toIsLocalRing := hloc, is_henselian := ?_ }
  intro f hf a₀ hfa₀ hf'a₀

  obtain ⟨i', b₀, hb₀⟩ : ∃ (i : EtNbhd R) (b : i.B), Hens.of i b = a₀ :=
    Ring.DirectLimit.exists_of a₀
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood R i' b₀
  set ρ := algebraMap R (Hens R) r with hρdef
  have hρ : a₀ - ρ ∈ maximalIdeal (Hens R) := by
    haveI := hofloc i'
    rw [← hb₀, hρdef, ← GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i' r, ← map_sub]; exact map_nonunit _ _ hr
  have hfρ : f.eval ρ ∈ maximalIdeal (Hens R) := by
    have hd := sub_dvd_eval_sub ρ a₀ f
    have : f.eval ρ - f.eval a₀ ∈ maximalIdeal (Hens R) := by
      obtain ⟨c, hc⟩ := hd
      rw [hc]; apply Ideal.mul_mem_right
      have := (Ideal.neg_mem_iff _).2 hρ; simpa using this
    simpa using Ideal.add_mem _ this hfa₀
  have hf'ρ : IsUnit (f.derivative.eval ρ) := by
    refine isUnit_of_sub_mem_maximalIdeal hf'a₀ ?_
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub ρ a₀ (derivative f)
    rw [hc]; apply Ideal.mul_mem_right
    have := (Ideal.neg_mem_iff _).2 hρ; simpa using this

  obtain ⟨i, g, hg⟩ : ∃ (i : EtNbhd R) (g : Polynomial i.B), g.map (Hens.of i) = f :=
    Ring.DirectLimit.Polynomial.exists_of (f' := fun _ _ h => EtNbhd.trans h) f
  haveI := hofloc i
  have hgm : g.Monic := monic_of_injective (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R i) (hg ▸ hf)
  let M := i.q.primeCompl
  let ψ : i.A →+* i.B := algebraMap i.A i.B
  let s : M := IsLocalization.commonDenom M g.support g.coeff
  have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M g
    (by rw [hgm.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨h, hhmap, -, hhm⟩ := lifts_and_natDegree_eq_and_monic hl
    ((monic_scaleRoots_iff _).2 hgm)
  let Φ : i.A →+* Hens R := (Hens.of i).comp ψ
  let u : Hens R := Φ s
  have hu : IsUnit u := (IsLocalization.map_units i.B s).map (Hens.of i)
  have hΦr : Φ (algebraMap R i.A r) = ρ := by
    simp only [Φ, ψ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i r
  let a₀' : i.A := (s : i.A) * algebraMap R i.A r
  have hΦa₀' : Φ a₀' = u * ρ := by simp only [a₀', map_mul, hΦr]; rfl
  have hhΦ : h.map Φ = f.scaleRoots u := by
    rw [show Φ = (Hens.of i).comp ψ from rfl, ← Polynomial.map_map, hhmap, map_scaleRoots _ _ _
      (by rw [hgm.leadingCoeff, map_one]; exact one_ne_zero), hg]
    rfl
  have key1 : Φ (h.eval a₀') = u ^ f.natDegree * f.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, hhΦ, hΦa₀']
    exact scaleRoots_eval₂_mul (RingHom.id _) ρ u
  have key2 : Φ (h.derivative.eval a₀') = u ^ (f.natDegree - 1) * f.derivative.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, ← derivative_map, hhΦ, hΦa₀']
    exact eval_derivative_scaleRoots_mul f u ρ
  have hpt1 : i.pt (h.eval a₀') = 0 := by
    have hm : ψ (h.eval a₀') ∈ maximalIdeal i.B := by
      intro hun
      have : Φ (h.eval a₀') ∈ maximalIdeal (Hens R) := by
        rw [key1]; exact Ideal.mul_mem_left _ _ hfρ
      exact (mem_maximalIdeal _).1 this (hun.map (Hens.of i))
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).1 hm
    exact (RingHom.mem_ker).1 this
  have hpt2 : i.pt (h.derivative.eval a₀') ≠ 0 := by
    intro h0
    have hq : h.derivative.eval a₀' ∈ i.q := RingHom.mem_ker.2 h0
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
    have hΦm : Φ (h.derivative.eval a₀') ∈ maximalIdeal (Hens R) := map_nonunit (Hens.of i) _ hm
    rw [key2] at hΦm
    exact (mem_maximalIdeal _).1 hΦm ((hu.pow _).mul hf'ρ)
  obtain ⟨j, hij, c, hc, hcm⟩ := GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd R i h a₀' hhm hpt1 hpt2
  haveI := hofloc j
  have hofj : (Hens.of j).comp (EtNbhd.trans hij) = Hens.of i :=
    RingHom.ext fun x => Ring.DirectLimit.of_f hij x
  have hΦj : (Hens.of j).comp ((EtNbhd.trans hij).comp ψ) = Φ := by
    rw [← RingHom.comp_assoc, hofj]
  set c' := Hens.of j c
  have hroot : (f.scaleRoots u).eval c' = 0 := by
    rw [← hhΦ, ← hΦj, ← Polynomial.map_map, eval_map, eval₂_at_apply, hc.eq_zero, map_zero]
  have hcm' : c' - u * ρ ∈ maximalIdeal (Hens R) := by
    have := map_nonunit (Hens.of j) _ hcm
    rwa [map_sub, ← RingHom.comp_apply (Hens.of j) (EtNbhd.trans hij),
      ← RingHom.comp_apply ((Hens.of j).comp (EtNbhd.trans hij)) ψ, hofj,
      show (Hens.of i).comp ψ = Φ from rfl, hΦa₀'] at this
  refine ⟨↑hu.unit⁻¹ * c', ?_, ?_⟩
  · have hc' : c' = u * (↑hu.unit⁻¹ * c') := by
      rw [← mul_assoc, hu.mul_val_inv, one_mul]
    have e := scaleRoots_eval₂_mul (p := f) (RingHom.id _) (↑hu.unit⁻¹ * c') u
    simp only [RingHom.id_apply] at e
    change eval (u * _) _ = u ^ _ * eval _ f at e
    rw [← hc', hroot] at e
    exact (((hu.pow _).mul_right_eq_zero).1 e.symm)
  · have e1 : ↑hu.unit⁻¹ * c' - ρ = ↑hu.unit⁻¹ * (c' - u * ρ) := by
      rw [mul_sub, ← mul_assoc, hu.val_inv_mul, one_mul]
    have e2 : ↑hu.unit⁻¹ * c' - a₀ = (↑hu.unit⁻¹ * c' - ρ) - (a₀ - ρ) := by ring
    rw [e2, e1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hcm') hρ

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityComponentsSmoothGroupSchemeMulMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.IdCompMul

theorem mul_mem_of_field {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : Smooth G.hom) (k : Type) [Field k]
    (p : Spec (CommRingCat.of k) ⟶ S) (a b : Over.mk p ⟶ G)
    (ha : a.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))})
    (hb : b.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (a * b).left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  let F := Over.pullback p
  let G' : Over (Spec (CommRingCat.of k)) := F.obj G
  have hpt : ∀ z : (Spec (CommRingCat.of k) : Scheme), z = IsLocalRing.closedPoint k :=
    fun z => Subsingleton.elim _ _
  have hsec : η[G'].left ≫ pullback.fst G.hom p = p ≫ η[G].left := by
    have hc : pullback.fst (𝟙 S) p = pullback.snd (𝟙 S) p ≫ p := by
      simpa using pullback.condition (f := 𝟙 S) (g := p)
    simp [G', F, hc]
    exact pullback.lift_fst _ _ _
  have key := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback G.left S G'.left (Spec (CommRingCat.of k)) G.hom G'.hom p
    (pullback.fst G.hom p) η[G].left η[G'].left hG (IsPullback.of_hasPullback G.hom p)
    (Over.w η[G]) (Over.w η[G']) hsec
  have huniv : ∀ t : (Spec (CommRingCat.of k) : Scheme), G'.hom ⁻¹' {t} = Set.univ :=
    fun t => Set.eq_univ_of_forall fun y => Set.mem_singleton_iff.mpr ((hpt _).trans (hpt t).symm)
  have hq : ∀ z : G'.left,
      pullback.fst G.hom p z ∈
        {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} ↔
      z ∈ connectedComponent ((η[G']).left (IsLocalRing.closedPoint k)) := by
    intro z
    rw [← Set.mem_preimage, key]
    show z ∈ connectedComponentIn (G'.hom ⁻¹' {G'.hom z}) ((η[G']).left (G'.hom z)) ↔ _
    rw [huniv, connectedComponentIn_univ, hpt (G'.hom z)]
  let u : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ F.obj (Over.mk p) :=
    Over.homMk (pullback.lift (𝟙 _) (𝟙 _) (by simp)) (by simp [F]; exact pullback.lift_snd _ _ _)
  have hgen : ∀ c : Over.mk p ⟶ G, (u ≫ F.map c).left ≫ pullback.fst G.hom p = c.left := by
    intro c
    simp [u, F]
    erw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp]
  have hpoint : ∀ (c : Over.mk p ⟶ G) (t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G'),
      t.left ≫ pullback.fst G.hom p = c.left →
        pullback.fst G.hom p (t.left (IsLocalRing.closedPoint k)) = c.left (IsLocalRing.closedPoint k) := by
    intro c t h
    rw [← h]
    rfl
  have ha' := (hq _).1 (by rw [hpoint a _ (hgen a)]; exact ha)
  have hb' := (hq _).1 (by rw [hpoint b _ (hgen b)]; exact hb)
  have hm := GlobalTheory.T.mul_mem_identityComponent_of_rational' k G' (u ≫ F.map a) (u ≫ F.map b) ha' hb'
  have e1 := hgen (a * b)
  rw [Functor.map_mul, MonObj.comp_mul] at e1
  rw [← hpoint (a * b) _ e1]
  exact (hq _).2 hm

theorem mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ w : (G ⊗ G).left, (fst G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (snd G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (μ[G]).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G instG hG w h1 h2
  let κ := (G ⊗ G).left.residueField w
  let j : Spec (CommRingCat.of κ) ⟶ (G ⊗ G).left := (G ⊗ G).left.fromSpecResidueField w
  let p : Spec (CommRingCat.of κ) ⟶ S := j ≫ (G ⊗ G).hom
  let a : Over.mk p ⟶ G := Over.homMk (j ≫ (fst G G).left) (by simp [p])
  let b : Over.mk p ⟶ G := Over.homMk (j ≫ (snd G G).left) (by simp [p, pullback.condition])
  have hw : j (IsLocalRing.closedPoint κ) = w := Scheme.fromSpecResidueField_apply w _
  have hl : lift a b = (Over.homMk j rfl : Over.mk p ⟶ G ⊗ G) := by
    apply CartesianMonoidalCategory.hom_ext
    · ext1
      simp [a]
    · ext1
      simp [b]
  have hm := mul_mem_of_field G hG κ p a b
    (by
      convert h1 using 2
      exact congrArg (fst G G).left hw)
    (by
      convert h2 using 2
      exact congrArg (snd G G).left hw)
  rw [Hom.mul_def, Over.comp_left, hl] at hm
  convert hm using 2
  exact (congrArg (μ[G]).left hw).symm

end GlobalTheory.IdCompMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTorsorEtaleHeightOneAbhyankar
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem comap_map_C_mapRingHom {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (p₁ : Ideal A₁) :
    (p₁.map (Polynomial.C : A₁ →+* A₁[X])).comap (Polynomial.mapRingHom f) =
      (p₁.comap f).map (Polynomial.C : A →+* A[X]) := by
  ext g
  simp only [Ideal.mem_comap, Ideal.mem_map_C_iff, Polynomial.coe_mapRingHom, Polynomial.coeff_map]

theorem atPrime_isDomain_injective (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] :
    IsDomain (Localization.AtPrime QA) ∧
      Function.Injective (algebraMap A (Localization.AtPrime QA)) := by
  obtain ⟨hd, -⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A) QA
    (Localization.AtPrime QA)
  refine ⟨hd, ?_⟩
  haveI := hd
  haveI : Module.Flat (Polynomial A) (Localization.AtPrime QA) :=
    Module.Flat.trans (Polynomial A) EA (Localization.AtPrime QA)
  have h1 : Function.Injective (algebraMap (Polynomial A) (Localization.AtPrime QA)) :=
    FaithfulSMul.algebraMap_injective (Polynomial A) (Localization.AtPrime QA)
  have h2 : algebraMap A (Localization.AtPrime QA) =
      (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp (algebraMap A (Polynomial A)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [h2]
  exact h1.comp Polynomial.C_injective

theorem closureEtaleAt_of_mem_height_le_one : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], P₁.height ≤ 1 → algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ _ _ _ _ _ _ _ _ f i i₁ hf EA _ _ _ _ _ QA _ jA hcomp hj DA _ _ q actA
    hq hqu htor a ha hhyp P₁ _ hP₁ hfa
  obtain ⟨hRd, hRi⟩ := atPrime_isDomain_injective A EA QA
  obtain ⟨hR₁d, hR₁i⟩ := atPrime_isDomain_injective A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj)
  have hfa0 : f a ≠ 0 := fun h => ha (hf (by rw [h, map_zero]))
  obtain ⟨hp₁h, hX₁⟩ := GlobalTheory.T.height_one_contraction_of_etale_prime A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ (f a)
    hfa0 hfa hP₁
  obtain ⟨hph, π, hπ, y, hy⟩ := hhyp _ hp₁h (by rw [Ideal.mem_comap]; exact hfa)
  obtain ⟨⟨_, hdvr₁⟩, -⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ _
    hp₁h hX₁
  have hsq : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj)).comp (Polynomial.mapRingHom f) := by
    apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA),
      locBC_algebraMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA)]
    congr 1
    rw [inclE_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  have hPX : (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)).comap
      (algebraMap A[X] (Localization.AtPrime QA)) =
      ((P₁.comap (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comap f).map
        (Polynomial.C : A →+* A[X]) := by
    rw [Ideal.comap_comap, hsq, ← Ideal.comap_comap, hX₁, comap_map_C_mapRingHom]
  obtain ⟨⟨_, hdvr⟩, hirr⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A EA QA (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)) _
    hph hPX
  have hsqA : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A (Localization.AtPrime QA)) =
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp f := by
    apply RingHom.ext; intro x
    exact locBC_algebraMap_base f i i₁ EA QA jA hcomp hj x
  have hsqF : (fibBC f i i₁ EA QA jA hcomp hj hf).comp
      (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj)
        (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj) := by
    apply RingHom.ext; intro x
    exact fibBC_algebraMap f i i₁ EA QA jA hcomp hj hf x
  exact GlobalTheory.T.generic_fibre_base_change_injective A (Localization.AtPrime QA) hRi A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) hR₁i
    f hf _ hsqA _ hsqF DA q actA hq hqu htor P₁ hdvr₁ hdvr π (hirr π hπ)
    (algebraMap A₁ _ y) (by rw [← map_pow, hy, ← RingHom.comp_apply, ← hsqA, RingHom.comp_apply])

end GlobalTheory.KeyOriginBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevels
section
set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel

namespace GlobalTheory.FullLevel.Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem nsmul_cancel {n : ℕ} (hn : n ≠ 0) {x y : D.La} (h : n • x = n • y) : x = y := by
  apply D.unimod.1
  ext w
  have h1 := congrArg (fun t => D.EF t w) h
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (by exact_mod_cast hn) h1

theorem mem_of_dvd {M : ℕ} (hM : M ≠ 0) {x : D.La} (h : ∀ y, (M : ℤ) ∣ D.EF x y) : ∃ u, x = M • u := by
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  choose f hf using h
  let φ : D.La →ₗ[ℤ] ℤ :=
    { toFun := f
      map_add' := fun a b => by
        apply mul_left_cancel₀ hM'
        rw [mul_add, ← hf, ← hf, ← hf, map_add]
      map_smul' := fun c a => by
        apply mul_left_cancel₀ hM'
        rw [← hf, map_smul, hf]
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }
  obtain ⟨u, hu⟩ := D.unimod.2 φ
  refine ⟨u, D.unimod.1 ?_⟩
  ext w
  rw [map_nsmul, LinearMap.smul_apply, hu, hf, nsmul_eq_mul]
  rfl

theorem mem_lcm {M A : ℕ} (hM : M ≠ 0) {x u v : D.La} (hu : x = M • u) (hv : x = A • v) :
    ∃ w, x = Nat.lcm M A • w := by
  have hg : Nat.gcd M A ≠ 0 := fun h => hM (Nat.eq_zero_of_gcd_eq_zero_left h)
  refine ⟨Nat.gcdA M A • v + Nat.gcdB M A • u, nsmul_cancel hg ?_⟩
  rw [← mul_nsmul', Nat.gcd_mul_lcm, ← natCast_zsmul x, Nat.gcd_eq_gcd_ab, add_zsmul, smul_add]
  congr 1
  · rw [hv, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · rw [hu, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
  {N : ℕ} {z : kˣ} {ev : D.La → Q}

theorem ev_zero (h : IsSympLevel D act e N z ev) : ev 0 = 1 := (h.2.2.1 0).2 ⟨0, by simp⟩

theorem ev_nsmul (h : IsSympLevel D act e N z ev) (n : ℕ) (a : D.La) : ev (n • a) = ev a ^ n := by
  induction n with
  | zero => simp [ev_zero h]
  | succ n ih => rw [succ_nsmul, h.1, ih, pow_succ]

theorem ev_eq_iff (h : IsSympLevel D act e N z ev) (x y : D.La) : ev x = ev y ↔ ∃ b, x - y = N • b := by
  rw [← h.2.2.1]
  have h1 : ev x = ev (x - y) * ev y := by rw [← h.1, sub_add_cancel]
  rw [h1]
  exact mul_eq_right

theorem ev_pow_eq (h : IsSympLevel D act e N z ev) (hN : 0 < N) {A : ℕ} (hA : A ∣ N) {x y : D.La}
    (hxy : ev x ^ (N / A) = ev y ^ (N / A)) : ∃ b, x - y = A • b := by
  obtain ⟨m, hm⟩ := hA
  have hA0 : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
  have hd : N / A = m := by rw [hm, Nat.mul_div_cancel_left _ hA0]
  rw [hd, ← ev_nsmul h, ← ev_nsmul h, ev_eq_iff h] at hxy
  obtain ⟨b, hb⟩ := hxy
  refine ⟨b, nsmul_cancel hm0 ?_⟩
  rw [smul_sub, hb, hm, smul_smul, mul_comm]

end GlobalTheory.FullLevel.Uniq

namespace GlobalTheory.FullLevel

open Uniq

theorem isSympLevel_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H)
    {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c')
    {z : kˣ} (hz : IsPrimitiveRoot z l.M') {etaA eta ev ev' : D.La → Q}
    (h : IsSympLevel D act e l.M' z ev) (hi : Induces l etaA eta ev)
    (h' : IsSympLevel D act e l.M' z ev') (hi' : Induces l etaA eta ev') : ev = ev' := by
  have hM' := M'_pos l
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hex : ∀ a, ∃ x, ev x = ev' a := fun a =>
    (h.2.2.2.1 _).1 ((h'.2.2.2.1 _).2 ⟨a, rfl⟩)
  choose g hg using hex
  have h1 : ∀ a, ∃ b, g a - a = l.A • b := fun a =>
    ev_pow_eq h hM' (A_dvd_M' l) (by rw [hg, hi'.1, hi.1])
  have h2 : ∀ c ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), ∀ a : D.La, ∃ b, g (c • a) - c • a = l.M • b := by
    intro c hc a
    have hmem : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul hc Submodule.mem_top
    exact ev_pow_eq h hM' (M_dvd_M' l) (by rw [hg, hi'.2 _ hmem, hi.2 _ hmem])
  have h3 : ∀ a b, (l.M : ℤ) ∣ D.EF (g a) (g b) - D.EF a b := by
    intro a b
    have e1 := h.2.2.2.2 (g a) (g b)
    rw [hg, hg] at e1
    have e2 := he _ _ _ _ e1 (h'.2.2.2.2 a b)
    have e3 : z ^ (D.EF (g a) (g b) - D.EF a b) = 1 := by rw [zpow_sub, e2, mul_inv_cancel]
    exact (Int.natCast_dvd_natCast.2 (M_dvd_M' l)).trans ((hz.zpow_eq_one_iff_dvd _).1 e3)
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  funext a
  have h4 : ∃ u, m • (g a - a) = l.M • u := by
    obtain ⟨b, hb⟩ := h2 m hm a
    obtain ⟨c, hc⟩ := (ev_eq_iff h (m • g a) (g (m • a))).1 (by rw [h.2.1, hg, hg, h'.2.1])
    obtain ⟨t, ht⟩ := M_dvd_M' l
    refine ⟨t • c + b, ?_⟩
    rw [smul_add, smul_smul, ← ht, ← hc, ← hb, smul_sub]
    abel
  have h5 : ∃ u, n • (g a - a) = l.M • u := by
    refine mem_of_dvd hM fun y => ?_
    obtain ⟨b, hb⟩ := h2 (H.bar n) (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn) y
    have h6 := h3 a (H.bar n • y)
    rw [sub_eq_iff_eq_add] at hb
    rw [hb, map_add, map_nsmul, nsmul_eq_mul, add_sub_assoc, dvd_add_right (dvd_mul_right _ _)] at h6
    rw [D.adj, map_sub, LinearMap.sub_apply]
    exact h6
  obtain ⟨u, hu⟩ := h4
  obtain ⟨v, hv⟩ := h5
  obtain ⟨b, hb⟩ := h1 a
  have h7 : g a - a = l.M • (v + u) := by rw [smul_add, ← hu, ← hv, ← add_smul, hnm, one_smul]
  rw [← hg]
  exact ((ev_eq_iff h _ _).2 (mem_lcm hM h7 hb)).symm

end GlobalTheory.FullLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfComponentsIntoGroupSchemeProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.Serre

theorem isMonHom_of_components : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ := by
  intro T A' B' C _ _ _ r pr' hpr huniv Φ hΦ
  have hcomp : ∀ u, IsMonHom (pr' u) := hpr
  have hΦu : ∀ u, IsMonHom (Φ ≫ pr' u) := hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := huniv (𝟙_ (Over T)) (fun u => η[C] ≫ Φ ≫ pr' u)
    have h1 : η[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (η[B'] : 𝟙_ (Over T) ⟶ B') = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [IsMonHom.one_hom, IsMonHom.one_hom (Φ ≫ pr' u)])
    rw [h1, h2]
  · obtain ⟨x, -, hx⟩ := huniv (C ⊗ C) (fun u => μ[C] ≫ Φ ≫ pr' u)
    have h1 : μ[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (Φ ⊗ₘ Φ) ≫ μ[B'] = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [Category.assoc, IsMonHom.mul_hom (Φ ≫ pr' u), IsMonHom.mul_hom (pr' u),
        ← Category.assoc, tensorHom_comp_tensorHom])
    rw [h1, h2]

end GlobalTheory.Serre
end

