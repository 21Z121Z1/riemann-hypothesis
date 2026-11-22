import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFinite
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem lineFin : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  intro k F _ _ _ _ _ hFF n g hg
  obtain ⟨hdet, hfin⟩ := hg
  refine ⟨hfin.subset ?_, fun w hw => ⟨?_, fun v h => hw (Matrix.eq_zero_of_mulVec_eq_zero (hdet v) h)⟩⟩
  · intro v hv hu
    apply hv
    simp [ord, hu.2]
  · let S : Set (Place k F) := {v | ¬ Unimod v (g v)} ∪
      ⋃ i ∈ {i : Fin n | w i ≠ 0}, {v : Place k F | v.1 (w i) ≠ 1}
    have hS : S.Finite := hfin.union (Set.Finite.biUnion (Set.toFinite _)
      fun i hi => ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1))
    refine hS.subset fun v hv => ?_
    by_contra hvS
    simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hvS
    obtain ⟨hu, hw1⟩ := hvS
    apply hv
    rw [(((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1) n (g v) w hu)]
    obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push_neg at h; exact hw (funext h)
    have h1 : ∀ i, v.1 (w i) ≤ 1 := by
      intro i
      by_cases hi : w i = 0
      · simp [hi]
      · exact le_of_eq (hw1 i hi)
    apply le_antisymm
    · exact Finset.sup_le fun i _ => h1 i
    · have := Finset.le_sup (f := fun i => v.1 (w i)) (Finset.mem_univ i0)
      have e : v.1 (w i0) = 1 := hw1 i0 hi0
      rw [e] at this; exact this

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomology
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem exists_cob_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (f : Z1 (OAff s'))
    (g : ∀ p : Pair φ, (OAff s').obj (op p.1.1))
    (hg : ∀ (p q : Pair φ) (hqp : q ≤ p), f.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
      g q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g p)) :
    ∃ G : C0 (OAff s'), d0 (OAff s') G = f.1 ∧ ∀ (W : X'.affineOpens) (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op (G (op W)) = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
  have ex : ∀ W : X'.affineOpens, ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op G = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
    intro W
    refine GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs φ s' W _ fun p q hp hq hqp ↦ ?_
    have e := Z1.comp f (homOfLE hp).op (homOfLE (Pair.le_fst hqp)).op
    rw [show (homOfLE hp).op ≫ (homOfLE (Pair.le_fst hqp)).op = (homOfLE hq).op from rfl, hg p q hqp] at e
    rw [map_sub, e]
    ring
  choose G hG using ex
  refine ⟨fun T ↦ G T.unop, ?_, hG⟩
  funext T T' a
  refine sec_eq_of_pair φ s' T'.unop _ _ fun p hp ↦ ?_
  have e1 := Z1.comp f a (homOfLE hp).op
  have e2 : a ≫ (homOfLE hp).op = (homOfLE (hp.trans (leOfHom a.unop))).op := rfl
  rw [e2] at e1
  rw [amitsur_d0_apply, map_sub, ← mp_comp, e2, hG, hG]
  linear_combination e1

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential

theorem pairRes_injective : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧
      Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  intro R' _ X X' φ s'
  refine ⟨?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    obtain ⟨G, hG, -⟩ := exists_cob_of_pair φ s' f (fun p ↦ g (op p)) fun p q hqp ↦
      (congrFun (congrFun (congrFun hg (op p)) (op q)) (homOfLE hqp).op).symm
    exact H1.mk_eq_zero.2 ⟨G, hG⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    have h0 : ∀ p : Pair φ, ω.1 (op p.1.1) = 0 := fun p ↦
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) (op p) _).symm.trans
        (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 (op p)) hω)
    refine Subtype.ext (funext fun W ↦ GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop _ fun p hp ↦ ?_)
    rw [← ω.2 (homOfLE hp).op]
    exact h0 p
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Hyp1.mk_surjective _ c
    rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ p : Pair φ, (OAff s').obj (op p.1.1) := fun p ↦ g (op p)
    have hf : ∀ (p q : Pair φ) (hqp : q ≤ p), z.1.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
        g' q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g' p) := fun p q hqp ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.1 (op p) (op q) (homOfLE hqp).op) hg).symm
    have hω : ∀ p : Pair φ, D R' _ (g' p) = z.1.2 (op p.1.1) := fun p ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.2 (op p)) hg).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor _ _ _ _)
    obtain ⟨G, hG, hGp⟩ := exists_cob_of_pair φ s' (cechDeRhamTotalCocyclesOne.fn _ z) g' hf
    refine Hyp1.mk_eq_zero.2 ⟨G, Tot1.ext (fun T T' a ↦ congrFun (congrFun (congrFun hG T) T') a)
      fun W ↦ ?_⟩
    refine (sub_eq_zero.1 (GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop (D R' _ (G W) - z.1.2 W) fun p hp ↦ ?_))
    have e := cechDeRhamTotalCocyclesOne.conn z (homOfLE hp).op
    rw [map_sub, p1_D, hGp, map_sub, hω]
    change _ - (p1 _ _ _) = _
    rw [e, show ((cechDeRhamTotalCocyclesOne.fn (OAff s') z : Z1 (OAff s')) : C1 (OAff s')) = z.1.1 from rfl]
    abel

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisObjectsUnitLociCoverAbove
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
private lemma covBy_of_covBy_localizations {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : C → Prop) (hLoc : _root_.GlobalTheory.CatCoh.Desc.HasLoc F) (T : C)
    {n : ℕ} (c : Fin n → F.obj T) (hc : Ideal.span (Set.range c) = ⊤)
    (h : ∀ (j : Fin n) (L : C) (l : T ⟶ L), IsUnit (_root_.GlobalTheory.CatCoh.mp F l (c j)) →
      (∀ (S : C) (w : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F w (c j)) → ∃! v, l ≫ v = w) →
      _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P L) :
    _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P T := by
  have hL := fun j => hLoc T (c j)
  choose L l hlu hsurj hker huniv using hL
  have hcov := fun j => h j (L j) (l j) (hlu j) (huniv j)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy at hcov
  choose m e he hP using hcov
  choose N x hx using fun j k => hsurj j (e j k)
  let b' : (Σ j : Fin n, Fin (m j)) → F.obj T := fun p => x p.1 p.2 * c p.1
  have hspan' : Ideal.span (Set.range b') = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff, ← hc, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : (1 : F.obj (L j)) ∈ Ideal.span (Set.range (e j)) := by
      rw [he j]; exact Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    choose N' s hs using fun k => hsurj j (r k)
    have hq : ∀ k, ∃ q, (∑ k', (N' k' + N j k')) = N' k + N j k + q := fun k =>
      Nat.exists_eq_add_of_le (Finset.single_le_sum (f := fun k' => N' k' + N j k')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    choose q hq using hq
    have hterm : ∀ k, _root_.GlobalTheory.CatCoh.mp F (l j) (s k * x j k * c j ^ q k) =
        (r k • e j k) * _root_.GlobalTheory.CatCoh.mp F (l j) (c j) ^ (∑ k', (N' k' + N j k')) := by
      intro k
      rw [map_mul, map_mul, map_pow, ← hs k, ← hx j k, hq k, pow_add, pow_add, smul_eq_mul]
      ring
    have hz : _root_.GlobalTheory.CatCoh.mp F (l j)
        (c j ^ (∑ k', (N' k' + N j k')) - ∑ k, s k * x j k * c j ^ q k) = 0 := by
      rw [map_sub, map_sum, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, hr,
        one_mul, map_pow, sub_self]
    obtain ⟨M, hM⟩ := hker j _ hz
    refine ⟨M + (∑ k', (N' k' + N j k')) + 1, ?_⟩
    have h2 : c j ^ M * c j ^ (∑ k', (N' k' + N j k')) =
        c j ^ M * ∑ k, s k * x j k * c j ^ q k := by
      rw [← sub_eq_zero, ← mul_sub]; exact hM
    have h3 : c j ^ (M + (∑ k', (N' k' + N j k')) + 1) =
        ∑ k, (c j ^ M * s k * c j ^ q k) * b' ⟨j, k⟩ := by
      rw [pow_succ, pow_add, h2, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [b']
      ring
    rw [h3]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, k⟩, rfl⟩)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  let eqv := Fintype.equivFin (Σ j : Fin n, Fin (m j))
  refine ⟨Fintype.card (Σ j : Fin n, Fin (m j)), b' ∘ eqv.symm, ?_, ?_⟩
  · rw [Set.range_comp, eqv.symm.range_eq_univ, Set.image_univ]
    exact hspan'
  · intro i S w hw
    change IsUnit (_root_.GlobalTheory.CatCoh.mp F w
      (x (eqv.symm i).1 (eqv.symm i).2 * c (eqv.symm i).1)) at hw
    generalize eqv.symm i = p at hw
    obtain ⟨j, k⟩ := p
    rw [map_mul, IsUnit.mul_iff] at hw
    obtain ⟨hxw, hcw⟩ := hw
    obtain ⟨v, hv, -⟩ := huniv j S w hcw
    apply hP j k S v
    have hfac : _root_.GlobalTheory.CatCoh.mp F w (x j k) = _root_.GlobalTheory.CatCoh.mp F v (e j k) *
        (_root_.GlobalTheory.CatCoh.mp F v (_root_.GlobalTheory.CatCoh.mp F (l j) (c j))) ^ (N j k) := by
      rw [← hv, _root_.GlobalTheory.CatCoh.mp_comp, ← hx j k, map_mul, map_pow]
    rw [hfac, IsUnit.mul_iff] at hxw
    exact hxw.1

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in

theorem _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → _root_.GlobalTheory.CatCoh.Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (t : C') (u : T ⟶ G.obj t), _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), (∃ i, IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ G.map a) (d i))) ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) := by
  intro R _ C _ C' _ F G _ _ hLoc hbasis hB T n d hd t u
  apply covBy_of_covBy_localizations F _ hLoc (G.obj t)
    (fun j => _root_.GlobalTheory.CatCoh.mp F u (d j)) (_root_.GlobalTheory.CatCoh.Desc.Basis.span_map_eq_top F u hd)
  intro j L l hl _
  obtain ⟨m, e, he, hfac⟩ := hbasis L
  apply covBy_of_covBy_localizations F _ hLoc L e he
  intro k L' l' hl' _
  obtain ⟨t'', v₁, v₂, -⟩ := hfac k L' l' hl'
  obtain ⟨p, f, hf, hP⟩ := hB t t'' L' (l ≫ l') v₂
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  refine ⟨p, f, hf, ?_⟩
  intro i S'' z hz
  obtain ⟨t₃, ⟨c₁⟩, ⟨c₂⟩, ⟨w⟩⟩ := hP i S'' z hz
  refine ⟨t₃, c₁, ⟨j, ?_⟩, ⟨w⟩⟩
  have hunit : IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ l ≫ v₁ ≫ G.map c₂) (d j)) := by
    rw [_root_.GlobalTheory.CatCoh.mp_comp]
    exact _root_.GlobalTheory.CatCoh.Desc.isUnit_comp (v₁ ≫ G.map c₂) hl
  rwa [show u ≫ G.map c₁ = u ≫ l ≫ v₁ ≫ G.map c₂ from Subsingleton.elim _ _]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGL
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NormFibre

theorem card_conj_mul_card_commute {G : Type} [Group G] (g : G) :
    Nat.card {g' : G // IsConj g g'} * Nat.card {x : G // Commute x g} = Nat.card G := by
  have e1 : {g' : G // IsConj g g'} ≃ MulAction.orbit (ConjAct G) g :=
    Equiv.subtypeEquivRight (fun g' => by rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  have e2 : {x : G // Commute x g} ≃ MulAction.stabilizer (ConjAct G) g :=
    { toFun := fun x => ⟨ConjAct.toConjAct x.1, by
          rw [MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul, x.2.eq, mul_inv_cancel_right]⟩
      invFun := fun y => ⟨ConjAct.ofConjAct y.1, by
          have h := y.2
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at h
          exact h⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) g),
    Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm]

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem galAct_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    galAct F F' n t (incl F F' n γ) = incl F F' n γ := by
  ext i j
  simp [galAct_apply, gal, incl]

theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  ext i j
  simp [galAct_apply, gal]

end Fields

section Count

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

def nrmFibreEquivOf (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (y : GL (Fin n) F') (hy : y * c * y⁻¹ = g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  have htw := (GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n).2.2.1
  { toFun := fun δ => ⟨y⁻¹ * δ.1 * galAct F F' n s y, by
        rw [htw, δ.2, ← hy]; group⟩
    invFun := fun ε => ⟨y * ε.1 * galAct F F' n s y⁻¹, by
        have := htw ε.1 y⁻¹
        rw [inv_inv] at this
        rw [this, ε.2, hy]⟩
    left_inv := fun δ => by
      apply Subtype.ext
      simp only [map_inv]
      group
    right_inv := fun ε => by
      apply Subtype.ext
      simp only [map_inv]
      group }

def nrmFibreEquiv (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (h : IsConj c g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  nrmFibreEquivOf s hs _ (isConj_iff.1 h).choose_spec

theorem card_isConj_nrm (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    (c : GL (Fin n) F') :
    Nat.card {δ : GL (Fin n) F' // IsConj c (nrm s δ)} =
      Nat.card {g' : GL (Fin n) F' // IsConj c g'} * Nat.card {δ : GL (Fin n) F' // nrm s δ = c} := by
  have e : {δ : GL (Fin n) F' // IsConj c (nrm s δ)} ≃
      Σ g' : {g' : GL (Fin n) F' // IsConj c g'}, {δ : GL (Fin n) F' // nrm s δ = g'.1} :=
    { toFun := fun δ => ⟨⟨nrm s δ.1, δ.2⟩, ⟨δ.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      left_inv := fun δ => rfl
      right_inv := fun p => by
        rcases p with ⟨⟨g', hg⟩, ⟨δ, hδ⟩⟩
        dsimp only at hδ
        subst hδ
        rfl }
  rw [← Nat.card_prod]
  exact Nat.card_congr (e.trans ((Equiv.sigmaCongrRight fun g' => nrmFibreEquiv s hs g'.2).trans
    (Equiv.sigmaEquivProd _ _)))

end Count

section Centraliser

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem card_nrm_eq_mul_card_commute (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s)
    (n : ℕ) (γ : GL (Fin n) F) :
    Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} * Nat.card {x : GL (Fin n) F // Commute x γ} =
      Nat.card {x : GL (Fin n) F' // Commute x (incl F F' n γ)} := by
  obtain ⟨-, hinj, -, hcomm, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  obtain ⟨δ₀, hδ₀B, hδ₀⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hcfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t => galAct_incl n t γ
  set c := incl F F' n γ with hc
  set B := Subalgebra.centralizer F' {(c : Matrix (Fin n) (Fin n) F')} with hB
  have memB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ↔ Commute x c := by
    intro x
    rw [hB, Subalgebra.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [Commute, SemiconjBy, Units.ext_iff, Units.val_mul, Units.val_mul]
    exact eq_comm
  have hcs : (c : Matrix (Fin n) (Fin n) F').map s = c := by rw [← galAct_coe, hcfix]
  have hstab : ∀ x ∈ B, x.map s ∈ B := by
    intro x hx
    rw [hB, Subalgebra.mem_centralizer_iff] at hx ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hx ⊢
    have e1 : ((c : Matrix (Fin n) (Fin n) F') * x).map s = ((c : Matrix (Fin n) (Fin n) F').map s) * x.map s :=
      Matrix.map_mul (f := (s : F' →+* F'))
    have e2 : (x * (c : Matrix (Fin n) (Fin n) F')).map s = x.map s * ((c : Matrix (Fin n) (Fin n) F').map s) :=
      Matrix.map_mul (f := (s : F' →+* F'))
    rw [hcs] at e1 e2
    rw [← e1, ← e2, hx]
  have h90 := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B hstab
  have hδ₀comm : ∀ e : GL (Fin n) F', Commute e c → Commute δ₀ e := by
    intro e he
    have hle : Algebra.adjoin F' {(c : Matrix (Fin n) (Fin n) F')} ≤
        Subalgebra.centralizer F' {(e : Matrix (Fin n) (Fin n) F')} := by
      apply Algebra.adjoin_le
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, ← Units.val_mul, ← Units.val_mul, he.eq]
    have h1 := hle hδ₀B
    rw [Subalgebra.mem_centralizer_iff] at h1
    have h2 := h1 _ rfl
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h2.symm)
  have hδ₀c : Commute δ₀ c := hδ₀comm c (Commute.refl c)
  have key : ∀ ε : GL (Fin n) F', Commute ε c → nrm s (δ₀ * ε) = c * nrm s ε := by
    intro ε hε
    rw [hmul δ₀ ε ?_, hδ₀]
    intro t u
    have h3 : Commute δ₀ (galAct F F' n (t⁻¹ * u) ε) := by
      apply hδ₀comm
      have := hε.map (galAct F F' n (t⁻¹ * u))
      rwa [hcfix] at this
    have h4 := h3.map (galAct F F' n t)
    have e : galAct F F' n t (galAct F F' n (t⁻¹ * u) ε) = galAct F F' n u ε := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    rwa [e] at h4
  have hYcomm : ∀ δ : GL (Fin n) F', nrm s δ = c → Commute δ c := by
    intro δ h
    have := hcomm δ
    rw [h, hcfix] at this
    exact this
  have eY : {δ : GL (Fin n) F' // nrm s δ = c} ≃
      {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} :=
    { toFun := fun δ => ⟨δ₀⁻¹ * δ.1, (memB _).2 (hδ₀c.inv_left.mul_left (hYcomm _ δ.2)), by
          have := key (δ₀⁻¹ * δ.1) (hδ₀c.inv_left.mul_left (hYcomm _ δ.2))
          rw [mul_inv_cancel_left, δ.2] at this
          simpa using this.symm⟩
      invFun := fun ε => ⟨δ₀ * ε.1, by rw [key _ ((memB _).1 ε.2.1), ε.2.2, mul_one]⟩
      left_inv := fun δ => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun ε => Subtype.ext (inv_mul_cancel_left _ _) }
  have eC' : {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} ≃ {x : GL (Fin n) F' // Commute x c} :=
    Equiv.subtypeEquivRight memB
  have eC : {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} ≃
      {x : GL (Fin n) F // Commute x γ} :=
    Equiv.subtypeEquivRight fun x => by
      rw [memB]
      exact ⟨fun h => hinj (by simpa only [map_mul] using h.eq), fun h => h.map _⟩
  rw [Nat.card_congr eY, ← Nat.card_congr eC, ← Nat.card_congr eC']
  exact h90

end Centraliser

theorem card_isNorm_mul_card : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F),
    Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) =
      Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  intro F F' _ _ _ _ s hs n γ
  have hX : Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} =
      Nat.card {g' : GL (Fin n) F' // IsConj (incl F F' n γ) g'} *
        Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} :=
    card_isConj_nrm s hs (incl F F' n γ)
  have hY := card_nrm_eq_mul_card_commute s hs n γ
  have h1 := card_conj_mul_card_commute (incl F F' n γ)
  have h2 := card_conj_mul_card_commute γ
  rw [hX, ← h2, ← h1, ← hY]
  ring

end GlobalTheory.Shin.NormFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  first | exact @GlobalTheory.CMVal.OrderUnits.orderC_units | exact GlobalTheory.CMVal.OrderUnits.orderC_units | (intros; apply GlobalTheory.CMVal.OrderUnits.orderC_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.EigLineSum

theorem ringHom_eq_of_eq_on_orderC {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K]
    {c : Ideal (OF E)} (hc : c ≠ ⊥) {σ σ' : E →+* K} (h : ∀ a : orderC c, σ a = σ' a) : σ = σ' := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  set b' : 𝓞 E := algebraMap (OF E) (𝓞 E) b with hb'
  have hb'0 : algebraMap (𝓞 E) E b' ≠ 0 := by
    have : algebraMap (𝓞 E) E b' = algebraMap (OF E) E b := rfl
    rw [this]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF E) E)).2 hb0
  have hmem : ∀ z : 𝓞 E, algebraMap (𝓞 E) E (b' * z) ∈ orderC c := fun z =>
    Subring.subset_closure (Or.inr ⟨b' * z, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), rfl⟩)
  have hb'mem : algebraMap (𝓞 E) E b' ∈ orderC c := by simpa using hmem 1
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun z => ?_)
  have h1 : σ (algebraMap (𝓞 E) E (b' * z)) = σ' (algebraMap (𝓞 E) E (b' * z)) := h ⟨_, hmem z⟩
  have h2 : σ (algebraMap (𝓞 E) E b') = σ' (algebraMap (𝓞 E) E b') := h ⟨_, hb'mem⟩
  have h3 : σ (algebraMap (𝓞 E) E b') ≠ 0 := (map_ne_zero σ).2 hb'0
  simp only [map_mul] at h1
  rw [h2] at h1 h3
  simpa using mul_left_cancel₀ h3 h1

theorem eigK_isInternal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) := by
  intro E _ _ _ c hc l _ O _ _ _ _ K _ _ _ _ hcard D _ _ I _ φ _ H _ _ ρ Fil B hL
  obtain ⟨hfree, hfin, hrank, hline, -⟩ := hL
  let f : orderC c → Module.End K (K ⊗[O] H) := fun a => (ρ a).baseChange K
  have hcomm : ∀ a b, Commute (f a) (f b) := fun a b => by
    show (ρ a).baseChange K * (ρ b).baseChange K = (ρ b).baseChange K * (ρ a).baseChange K
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have hind0 := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have hinj : Function.Injective (fun σ : E →+* K => fun a : orderC c => σ a) := fun σ σ' h =>
    ringHom_eq_of_eq_on_orderC hc (fun a => congrFun h a)
  have hind : iSupIndep (fun σ : E →+* K => eigK ρ σ) :=
    (hind0.comp hinj).mono fun σ => iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  haveI : Finite (E →+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  haveI := Fintype.ofFinite (E →+* K)
  have htot : Module.finrank K (K ⊗[O] H) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, hrank]
  have hinjD : Function.Injective (DirectSum.coeLinearMap (fun σ : E →+* K => eigK ρ σ)) :=
    hind.dfinsupp_lsum_injective
  have hdim : Module.finrank K (DirectSum (E →+* K) fun σ => eigK ρ σ) = Module.finrank K (K ⊗[O] H) := by
    rw [Module.finrank_directSum, htot, ← hcard, Nat.card_eq_fintype_card]
    simp [hline]
  exact ⟨hinjD, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinjD⟩

end GlobalTheory.EigLineSum
end
end

