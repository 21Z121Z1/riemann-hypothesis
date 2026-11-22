import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.SemistableReduction.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddi
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ChernSpec

open GlobalTheory.EtC.ClsSpec

set_option backward.isDefEq.respectTransparency false

theorem sec_neg {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) {U : Scheme.{0}}
    (a b : Sec ((res R F).X s) U) : a = b := by
  have hZ : IsZero ((res R F).X s) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs
  have h := hZ.eq_of_src (𝟙 _) 0
  have ha : Sec.map (𝟙 _) a = Sec.map (0 : (res R F).X s ⟶ _) a := by rw [h]
  have hb : Sec.map (𝟙 _) b = Sec.map (0 : (res R F).X s ⟶ _) b := by rw [h]
  simp [Sec.map] at ha hb
  rw [ha, hb]

theorem lineUnit_face_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 2 U) (i : Fin 3) :
    lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := by
  rw [← face_res, ClsSpec.lineUnit_res]

theorem rep_unique (q : ℕ) [NeZero q] {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1))
    (γ γ' : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w))
    (h0' : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ' 0 2 (by simp) U x = 0)
    (h1' : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ' 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2' : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ' 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s hs U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 2 := by omega
    rw [h0, h0']
  | 1 =>
    obtain rfl : s = 1 := by omega
    refine ClsSpec.sep (ClsSpec.loc_mono (root_loc (hE U ⟨x.face 0⟩) (lineUnit L x)) fun V g ⟨v, hv⟩ => ?_)
    have hv' : v ^ q = lineUnit L (x.res g) := by rw [ClsSpec.lineUnit_res]; exact hv
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 1 1 _ V U g x,
      h1 V _ v hv', h1' V _ v hv']
  | 2 =>
    obtain rfl : s = 0 := by omega
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← lineUnit_face_res] at hv hw
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 2 0 _ V U g x,
      h2 V _ v w hv hw, h2' V _ v w hv hw]
  | p + 3 => exact sec_neg _ _ (by omega) _ _

theorem rep_comp (q : ℕ) {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1))
    (γ : Cochain ((chains (ZMod q)).obj E') (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E' 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E' 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E' 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) x →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 1 1 (by simp) U x =
        Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) (x.face 2) →
      w ^ q = lineUnit (f ≫ L) (x.face 0) →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 2 0 (by simp) U x =
        kumT q U v + kumT q U w - kumT q U (v * w)) := by
  refine ⟨fun U x => ?_, fun U x v hv => ?_, fun U x v w hv hw => ?_⟩
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h0 U _
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h1 U _ v hv
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]
    refine h2 U _ v w ?_ ?_
    · rw [← map_face]; exact hv
    · rw [← map_face]; exact hw

theorem face_forms (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w) :=
  fun U x v w hv hw => h2 U x v w (by rw [sub_zero_one]; exact hv) (by rw [sub_one_one]; exact hw)

theorem firstChernClassTateTwist_pullback (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) (hE' : Inv q E') :
    pull _ f _ _ (c1 q L) = c1 q (f ≫ L) := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨γ, hγ, h0, h1, h2⟩ := firstChernClassTateTwist_cocycle_representative q hE' L
  obtain ⟨γ', hγ', h0', h1', h2'⟩ := firstChernClassTateTwist_cocycle_representative q hE (f ≫ L)
  obtain ⟨k0, k1, k2⟩ := rep_comp q f L γ.1 h0 h1 (face_forms q L γ.1 h2)
  have key := rep_unique q hE (f ≫ L) _ γ'.1 k0 k1 k2 h0' h1' (face_forms q (f ≫ L) γ'.1 h2')
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) γ (zero_add 2)) = _
  congr 1
  exact Cocycle.ext key

end GlobalTheory.EtC.ChernSpec

namespace GlobalTheory.EtC.ChernSpec
open GlobalTheory.EtC.ClsSpec
set_option backward.isDefEq.respectTransparency false

theorem isOneCochain_add (q : ℕ) [NeZero q] {E : Spc} (L M N : E ⟶ ofCat (glCat 1)) (hE : Inv q E)
    (hN : ∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) :
    c1 q N = c1 q L + c1 q M := by
  obtain ⟨γL, hL, l0, l1, l2⟩ := firstChernClassTateTwist_cocycle_representative q hE L
  obtain ⟨γM, hM, m0, m1, m2⟩ := firstChernClassTateTwist_cocycle_representative q hE M
  obtain ⟨γN, hN', n0, n1, n2⟩ := firstChernClassTateTwist_cocycle_representative q hE N
  have l2' := face_forms q L γL.1 l2
  have m2' := face_forms q M γM.1 m2
  have n2' := face_forms q N γN.1 n2
  have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
  obtain ⟨b, hb, hbv⟩ : ∃ b : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 0) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (b U x) = b V (x.res g)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → w ^ q = lineUnit M x →
        b U x = kumT q U v + kumT q U w - kumT q U (v * w) := by
    rcases kumT_cases q with ht | ht
    · exact exists_two_family ht hq₁ (fun U x => lineUnit L x) (fun U x => lineUnit M x)
        (fun V U g x => ClsSpec.lineUnit_res L g x) (fun V U g x => ClsSpec.lineUnit_res M g x)
    · refine ⟨fun _ _ => 0, fun V U g x => map_zero _, fun U x v w _ _ => ?_⟩
      rw [ht]
      simp
  obtain ⟨β, hβ1, hβ0⟩ := exists_single (R := ZMod q) (E := E) (I := res _ (tw q 1)) (n := 1) 1 0 (by simp) b hb
  rw [← hL, ← hM, ← hN', eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_add, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨β, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, Cocycle.coe_add, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1,
    ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).1]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).1 x, hβ0 _ _ _ _ _ (by decide), smap_zero, l0, m0, n0]
    simp
  | 1 =>
    obtain rfl : t = 1 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 0 0 1 (by simp) ht x]
    rw [Finset.sum_eq_zero fun i _ => by rw [hβ0 _ _ _ _ _ (by decide), smul_zero], smul_zero, add_zero, hβ1]
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc (hq₁ U x) (lineUnit L x))
      (root_loc (hq₁ U x) (lineUnit M x))) fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← ClsSpec.lineUnit_res] at hv hw
    rw [res_map, hb, hbv V _ v w hv hw, res_sub, res_add,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 1 1 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 1 1 _ V U g x, l1 V _ v hv, m1 V _ w hw,
      n1 V _ (v * w) (by rw [mul_pow, hv, hw, hN]), smap_sub, smap_add]
  | 2 =>
    obtain rfl : t = 0 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 1 (-1) 0 (by simp) ht x]
    rw [hβ0 _ _ _ _ _ (by decide), smap_zero, zero_add, Fin.sum_univ_three, hβ1, hβ1, hβ1]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, ← sub_eq_add_neg]
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and
      (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      (ClsSpec.loc_and (root_loc hU (lineUnit M (x.face 2))) (root_loc hU (lineUnit M (x.face 0)))))
      fun V g ⟨⟨⟨a, ha⟩, c, hc⟩, ⟨a', ha'⟩, c', hc'⟩ => ?_)
    rw [← lineUnit_face_res] at ha hc ha' hc'
    have hN2 : ∀ i, lineUnit N ((x.res g).face i) = lineUnit L ((x.res g).face i) * lineUnit M ((x.res g).face i) :=
      fun i => hN V _
    simp only [res_add, res_sub, neg_one_sq, one_smul]
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 2 0 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 2 0 _ V U g x, l2' V _ a c ha hc, m2' V _ a' c' ha' hc',
      n2' V _ (a * a') (c * c') (by rw [mul_pow, ha, ha', hN2]) (by rw [mul_pow, hc, hc', hN2])]
    rw [hb, hb, hb, face_res, face_res, face_res,
      hbv V _ c c' (by rw [hc]) (by rw [hc']),
      hbv V _ (a * c) (a' * c') (by rw [lineUnit_face, mul_pow, ha, hc]) (by rw [lineUnit_face, mul_pow, ha', hc']),
      hbv V _ a a' ha ha']
    have e : a * c * (a' * c') = a * a' * (c * c') := by rw [mul_mul_mul_comm]
    rw [e]
    abel
  | p + 3 => exact sec_neg _ _ (by omega) _ _

end GlobalTheory.EtC.ChernSpec

theorem _root_.GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity : ∀ (q : ℕ) [NeZero q], (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk γ = c1 q L ∧ (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧ (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧ ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E → (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M := by
  intro q _
  exact ⟨fun L hE => firstChernClassTateTwist_cocycle_representative q hE L, fun f L hE' => GlobalTheory.EtC.ChernSpec.firstChernClassTateTwist_pullback q f L hE',
    fun L M N hE hN => GlobalTheory.EtC.ChernSpec.isOneCochain_add q L M N hE hN⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH2Bijective
section
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh

theorem fnMap_h2_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (h11 : K.M1.Ac1) (h12 : K.M1.Ac2)
    (h20 : K.M2.Ac0) (h21 : K.M2.Ac1) (h30 : K.M3.Ac0) : Function.Bijective K.fnMap.h2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = 0 at hc
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hc
    obtain ⟨⟨f, ω0⟩, hf⟩ := hc
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = a.1.1 T T' T'' φ ψ := by
      intro T T' T'' φ ψ
      have := congrArg (fun x => x.1 T T' T'' φ ψ) hf
      simp [Cx.D1, Cx.fnMap, CxMap.z2, CxMap.p2] at this
      exact this
    have ha := a.2
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨ω, hω⟩ := h11 (fun T T' φ => a.1.2.1 T T' φ + K.d0 T' (f T T' φ)) (by
      intro T T' T'' φ ψ
      rw [ha2 T T' T'' φ ψ, ← hz T T' T'' φ ψ]
      simp only [map_add, map_sub, K.diffZero_natural]
      abel)
    have hη : (fun T => a.1.2.2 T - K.d1 T (ω T)) = 0 := by
      apply h20
      intro T T' φ
      have e := hω T T' φ
      have e2 : a.1.2.1 T T' φ = ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) := by
        rw [← e]; abel
      rw [ha3 T T' φ, e2]
      simp only [map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    refine ⟨(f, ω), ?_⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    · funext T T' φ
      have e := hω T T' φ
      change ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = _
      rw [← e]; abel
    · funext T
      have e := congrFun hη T
      change K.d1 T (ω T) = _
      simp only [Pi.zero_apply, sub_eq_zero] at e
      exact e.symm
  · intro c
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨hb1, -, -, -⟩ := b.2
    obtain ⟨f, hf⟩ := h12 (fun T T' T'' φ ψ => K.d0 T'' (b.1.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      rw [← K.diffZero_natural, ← map_add, hb1, map_add])
    obtain ⟨g, hg⟩ := h21 (fun T T' φ => K.d1 T' (-f T T' φ)) (by
      intro T T' T'' φ ψ
      have e := hf T T' T'' φ ψ
      have e2 : f T T'' (φ ≫ ψ) = K.M1.map ψ (f T T' φ) + f T' T'' ψ - K.d0 T'' (b.1.1 T T' T'' φ ψ) := by
        rw [e]; abel
      rw [e2]
      simp only [map_neg, map_add, map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel)
    have h3 : (fun T => K.d2 T (g T)) = 0 := by
      apply h30
      intro T T' φ
      have e := hg T T' φ
      have e2 : g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ) := by rw [e]; abel
      rw [e2, map_add, K.diffTwo_comp_diffOne, add_zero, K.diffTwo_natural]
    let a : K.Z2 := ⟨(b.1.1, fun T T' φ => -f T T' φ, g), by
      refine ⟨hb1, fun T T' T'' φ ψ => ?_, fun T T' φ => ?_, fun T => ?_⟩
      · rw [hf T T' T'' φ ψ]; simp only [map_neg, map_sub, map_add]; abel
      · have e := hg T T' φ
        change g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ)
        rw [e]; abel
      · exact congrFun h3 T⟩
    refine ⟨QuotientAddGroup.mk a, ?_⟩
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = QuotientAddGroup.mk b
    congr 1
end GlobalTheory.CxCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.QAtFormal

universe u

variable {C : Type u} [Category.{0} C] (K : Cx C)

theorem qAt_ident (T : C) : K.QAt (𝟙 T) := by
  refine ⟨fun x _ h => ?_, fun y hy => ⟨y, hy, ?_⟩, fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩,
    fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩⟩
  · rwa [K.M0.map_id] at h
  · exact K.M0.map_id T y
  · rw [K.M1.map_id] at h; exact h.symm
  · rw [K.M1.map_id, map_zero, add_zero]
  · rw [K.M2.map_id] at h; exact h.symm
  · rw [K.M2.map_id, map_zero, add_zero]

theorem qAt_comp {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (ha : K.QAt a) (hb : K.QAt b) :
    K.QAt (a ≫ b) := by
  refine ⟨fun x hx h => ?_, fun y hy => ?_, fun x y hx h => ?_, fun y hy => ?_,
    fun x y hx h => ?_, fun y hy => ?_⟩
  · rw [K.M0.map_comp] at h
    exact ha.inj0 x hx (hb.inj0 _ (by rw [K.diffZero_natural, hx, map_zero]) h)
  · obtain ⟨x', hx', rfl⟩ := hb.surj0 y hy
    obtain ⟨x, hx, rfl⟩ := ha.surj0 x' hx'
    exact ⟨x, hx, K.M0.map_comp a b x⟩
  · rw [K.M1.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj1 _ y (by rw [K.diffOne_natural, hx, map_zero]) h
    exact ha.inj1 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj1 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj1 x' hx'
    refine ⟨x, K.M0.map b w + w', hx, ?_⟩
    simp only [map_add, K.M1.map_comp, K.diffZero_natural]
    abel
  · rw [K.M2.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj2 _ y (by rw [K.diffTwo_natural, hx, map_zero]) h
    exact ha.inj2 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj2 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj2 x' hx'
    refine ⟨x, K.M1.map b w + w', hx, ?_⟩
    simp only [map_add, K.M2.map_comp, K.diffOne_natural]
    abel

theorem qAt_of_comp_retract {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T')
    (hbc : b ≫ c = 𝟙 T') (h : K.QAt (a ≫ b)) : K.QAt a := by
  have e0 : ∀ y, K.M0.map c (K.M0.map b y) = y := fun y => by
    rw [← K.M0.map_comp, hbc, K.M0.map_id]
  have e1 : ∀ y, K.M1.map c (K.M1.map b y) = y := fun y => by
    rw [← K.M1.map_comp, hbc, K.M1.map_id]
  have e2 : ∀ y, K.M2.map c (K.M2.map b y) = y := fun y => by
    rw [← K.M2.map_comp, hbc, K.M2.map_id]
  refine ⟨fun x hx hax => ?_, fun y hy => ?_, fun x y hx hxy => ?_, fun y hy => ?_,
    fun x y hx hxy => ?_, fun y hy => ?_⟩
  · exact h.inj0 x hx (by rw [K.M0.map_comp, hax, map_zero])
  · obtain ⟨x, hx, hxy⟩ := h.surj0 (K.M0.map b y) (by rw [K.diffZero_natural, hy, map_zero])
    refine ⟨x, hx, ?_⟩
    rw [K.M0.map_comp] at hxy
    simpa only [e0] using congrArg (K.M0.map c) hxy
  · exact h.inj1 x (K.M0.map b y) hx (by rw [K.M1.map_comp, hxy, K.diffZero_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj1 (K.M1.map b y) (by rw [K.diffOne_natural, hy, map_zero])
    refine ⟨x, K.M0.map c w, hx, ?_⟩
    have := congrArg (K.M1.map c) hw
    rw [map_add, K.M1.map_comp, e1, e1, ← K.diffZero_natural] at this
    exact this
  · exact h.inj2 x (K.M1.map b y) hx (by rw [K.M2.map_comp, hxy, K.diffOne_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj2 (K.M2.map b y) (by rw [K.diffTwo_natural, hy, map_zero])
    refine ⟨x, K.M1.map c w, hx, ?_⟩
    have := congrArg (K.M2.map c) hw
    rw [map_add, K.M2.map_comp, e2, e2, ← K.diffOne_natural] at this
    exact this

theorem qAt_of_isIso {T T' : C} (a : T ⟶ T') [IsIso a] : K.QAt a :=
  qAt_of_comp_retract K a (inv a) a (IsIso.inv_hom_id a) (by rw [IsIso.hom_inv_id]; exact qAt_ident K T)

theorem qAt_formal : ∀ (C : Type 1) [Category.{0} C] (K : Cx C),
    (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧
    (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧
    ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a :=
  fun _ _ K => ⟨fun _ _ a _ => qAt_of_isIso K a, fun _ _ _ a b => qAt_comp K a b,
    fun _ _ _ a b c => qAt_of_comp_retract K a b c⟩

end GlobalTheory.CxCoh.QAtFormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSectionSliceEqPolyDivDetPow
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem differentiable_det_of {r : ℕ} :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) := by
  have : (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) * ∏ i, y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [Matrix.of_apply]
  rw [this]
  fun_prop

theorem differentiable_update_frame {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {r : ℕ}
    (x : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => Function.update x τ y) := by
  intro y
  exact (hasFDerivAt_update x y).differentiableAt

end GlobalTheory

namespace GlobalTheory

theorem section_slice_eq_poly_div_det_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) [DecidableEq X.Ψ],
      (∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0) →
      ∀ (la : Wt X.Ψ r) (N : ℕ), (∀ τ i, 0 ≤ la τ i + N) →
      ∀ P : Frame X.Ψ r → ℂ, X.IsSec la P → ∀ x ∈ X.dom, ∀ τ : X.Ψ,
        ∃ F : MvPolynomial (Fin r × Fin r) ℂ, F.IsHomogeneous (∑ i, (la τ i + N).toNat) ∧
          ∀ y : Fin r → Fin r → ℂ, (Matrix.of y).det ≠ 0 →
            P (Function.update x τ y) =
              MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N := by
  intro E _ _ _ r X _ hdom la N hN P hP x hx τ
  classical

  have hupd : ∀ y : Fin r → Fin r → ℂ,
      Function.update x τ y ∈ X.dom ↔ (Matrix.of y).det ≠ 0 := by
    intro y
    rw [hdom]
    have hx' := (hdom x).1 hx
    constructor
    · intro h
      have := h τ
      simpa [mat] using this
    · intro h σ
      by_cases hσ : σ = τ
      · subst hσ
        simpa [mat] using h
      · simpa [mat, Function.update_of_ne hσ] using hx' σ
  let a : Fin r → ℕ := fun i => (la τ i + N).toNat
  let h : Matrix (Fin r) (Fin r) ℂ → ℂ := fun y =>
    P (Function.update x τ (fun i j => y i j)) * y.det ^ N

  have hholo : ReciprocityTheory.MultiplicativeHeights.IsHoloGL h := by
    unfold ReciprocityTheory.MultiplicativeHeights.IsHoloGL
    have h1 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => P (Function.update x τ y))
        {y | (Matrix.of y).det ≠ 0} :=
      hP.1.comp (differentiable_update_frame x τ).differentiableOn
        (fun y hy => (hupd y).2 hy)
    have h2 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det ^ N)
        {y | (Matrix.of y).det ≠ 0} :=
      (differentiable_det_of.pow N).differentiableOn
    exact h1.mul h2

  have htri : ReciprocityTheory.MultiplicativeHeights.IsTriEquivariant a h := by
    intro y b hy hb hbt
    let b' : Frame X.Ψ r := fun σ => if σ = τ then b else (1 : Matrix (Fin r) (Fin r) ℂ)
    have hbτ : b' τ = b := by exact if_pos rfl
    have hbσ : ∀ σ, σ ≠ τ → b' σ = (1 : Matrix (Fin r) (Fin r) ℂ) := fun σ hσ => by exact if_neg hσ
    have hb'B : b' ∈ Bor X.Ψ r := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbτ]; exact hb
        · rw [hbτ]; exact hbt hcd
      · refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbσ σ hσ]; change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0; simp
        · rw [hbσ σ hσ, Matrix.one_apply, if_neg (ne_of_lt hcd).symm]
    have hrm : rmul (Function.update x τ (fun i j => y i j)) b' =
        Function.update x τ (fun i j => (y * b) i j) := by
      funext σ
      by_cases hσ : σ = τ
      · subst hσ
        change (Matrix.of (Function.update x σ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x σ (fun i j => (y * b) i j) σ
        rw [hbτ, Function.update_self, Function.update_self]
        rfl
      · change (Matrix.of (Function.update x τ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x τ (fun i j => (y * b) i j) σ
        rw [hbσ σ hσ, Function.update_of_ne hσ, Function.update_of_ne hσ]
        exact Matrix.mul_one _
    have hbc : bchar la b' = ∏ i, b i i ^ la τ i := by
      unfold bchar
      rw [Finset.prod_eq_single τ]
      · rw [hbτ]
      · intro σ _ hσ
        rw [hbσ σ hσ]
        exact Finset.prod_eq_one fun i _ => by simp
      · intro h'; exact absurd (Finset.mem_univ τ) h'
    have hmem : Function.update x τ (fun i j => y i j) ∈ X.dom := (hupd _).2 hy
    have hP2 := hP.2.1 _ hmem b' hb'B
    rw [hrm, hbc] at hP2
    have hdb : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular hbt
    have hbii : ∀ i, b i i ≠ 0 := by
      intro i
      rw [hdb] at hb
      exact Finset.prod_ne_zero_iff.mp hb i (Finset.mem_univ i)
    have hchar : (∏ i, b i i ^ la τ i) * b.det ^ N = ReciprocityTheory.MultiplicativeHeights.triChar a b := by
      rw [hdb, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      unfold ReciprocityTheory.MultiplicativeHeights.triChar
      refine Finset.prod_congr rfl fun i _ => ?_
      have e : ((la τ i + N).toNat : ℤ) = la τ i + N := Int.toNat_of_nonneg (hN τ i)
      rw [← zpow_natCast (b i i) N, ← zpow_add₀ (hbii i), ← zpow_natCast, e]
    show P (Function.update x τ (fun i j => (y * b) i j)) * (y * b).det ^ N =
      ReciprocityTheory.MultiplicativeHeights.triChar a b * (P (Function.update x τ (fun i j => y i j)) * y.det ^ N)
    rw [hP2, Matrix.det_mul, mul_pow, ← hchar]
    ring
  obtain ⟨F, hF, hFe⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.bwPoly r a h hholo htri
  refine ⟨F, hF, fun y hy => ?_⟩
  have e := hFe (Matrix.of y) hy
  have e' : P (Function.update x τ y) * (Matrix.of y).det ^ N =
      MvPolynomial.eval (fun ij => y ij.1 ij.2) F := e
  rw [← e', inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy), mul_one]

end GlobalTheory
end

