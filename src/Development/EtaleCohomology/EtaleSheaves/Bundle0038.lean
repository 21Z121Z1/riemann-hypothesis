import Development.EtaleCohomology.EtaleSheaves.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.EtaleSheaves.Bundle0025

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwGenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec.Gen

theorem prim_pow_eq_one {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hu : IsUnit (q : K) := by simpa using ζ.2.1.map φ
  have : NeZero (q : K) := ⟨hu.ne_zero⟩
  have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at h
  have h2 : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by simpa using h
  rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def,
    Polynomial.isRoot_cyclotomic_iff] at h2

theorem exists_pow {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ ξ : Prim q A) :
    ∃ k < q, k.Coprime q ∧ φ ξ.1 = φ ζ.1 ^ k := by
  have hζ := prim_isPrimitiveRoot φ ζ
  have hξ := prim_isPrimitiveRoot φ ξ
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine ⟨i, hi, ?_, e.symm⟩
  exact (hζ.pow_iff_coprime (NeZero.pos q) i).mp (by rw [e]; exact hξ)

theorem key_ring {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (x y : A) (q k : ℕ) (hq : (q : K) ≠ 0)
    (hx : x ^ q = 1) (hy : y ^ q = 1) (h : φ x = φ y ^ k) :
    φ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) ≠ 0 ∧
    ∀ (B : Type) [CommRing B] (ψ : A →+* B), IsUnit (ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b)) →
      ψ x = ψ y ^ k := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hkq : k * (q - 1) + k = k * q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hq0); simp [mul_add]; ring
  have hyk : y ^ (k * (q - 1)) * y ^ k = 1 := by rw [← pow_add, hkq, mul_comm, pow_mul, hy, one_pow]
  have hu : (x * y ^ (k * (q - 1))) ^ q = 1 := by
    rw [mul_pow, hx, one_mul, ← pow_mul, mul_comm, pow_mul, hy, one_pow]
  refine ⟨?_, ?_⟩
  · have : φ (x * y ^ (k * (q - 1))) = 1 := by
      rw [map_mul, map_pow, h, ← pow_add, add_comm, hkq, mul_comm, pow_mul, ← map_pow, hy, map_one, one_pow]
    simpa [map_sum, map_pow, this] using hq
  · intro B _ ψ hs
    have h0 : ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) * (ψ (x * y ^ (k * (q - 1))) - 1) = 0 := by
      rw [← map_one ψ, ← map_sub, ← map_mul, geom_sum_mul, hu, sub_self, map_zero]
    have h1 : ψ (x * y ^ (k * (q - 1))) = 1 := by
      have := (hs.mul_right_eq_zero).mp h0
      exact sub_eq_zero.mp this
    calc ψ x = ψ x * ψ (y ^ (k * (q - 1)) * y ^ k) := by rw [hyk, map_one, mul_one]
      _ = ψ (x * y ^ (k * (q - 1))) * ψ y ^ k := by simp only [map_mul, map_pow]; ring
      _ = ψ y ^ k := by rw [h1, one_mul]

theorem isUnit_res {W : Scheme.{0}} (s : Γ(W, ⊤)) :
    IsUnit ((Scheme.Γ.map (W.basicOpen s).ι.op).hom s) := by
  set O := W.basicOpen s
  rw [Scheme.Γ_map_op]
  refine RingedSpace.isUnit_of_isUnit_germ O.toScheme.toRingedSpace ⊤ _ (fun y _ => ?_)
  have hy : y ∈ O.toScheme.basicOpen (O.ι.appTop s) := by
    rw [← Scheme.preimage_basicOpen_top]
    show O.ι y ∈ O
    exact y.2
  exact (Scheme.mem_basicOpen_top _ _ _).mp hy

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec.Gen

theorem map_mk {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    ((twF q j).map f).hom (Submodule.Quotient.mk (p := twRel q j A) (Finsupp.single ξ r)) =
      Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single (ξ.map f.hom) r) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ξ r)) = _
  rw [Finsupp.mapDomain_single]

theorem mk_pow {q : ℕ} (j : ℤ) {B : CommRingCat.{0}} (ζ ξ : Prim q B) (k : ℕ) (hk : k < q) (hc : k.Coprime q)
    (h : ξ.1 = ζ.1 ^ k) :
    (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ξ 1) : (twF q j).obj B) =
      ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) • twCls j ζ := by
  unfold twCls
  have h1 : (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) : ULift.{1} (ZMod q)) •
      (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q))) := by
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine Eq.trans ?_ h1.symm
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, ZMod.unitOfCoprime k hc, ?_, rfl⟩
  rw [h, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem res_le {q : ℕ} (j : ℤ) {W : Scheme.{0}} {O O' : W.Opens} (h : O' ≤ O) {x y : (twF q j).obj Γ(W, ⊤)}
    (e : ((twF q j).map (Scheme.Γ.map O.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom y) :
    ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom y := by
  rw [← W.homOfLE_ι h, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp]
  exact congrArg (ModuleCat.Hom.hom ((twF q j).map (Scheme.Γ.map (W.homOfLE h).op))) e

theorem core {q : ℕ} [NeZero q] (j : ℤ) {W : Scheme.{0}} (ζ ξ : Prim q Γ(W, ⊤)) (w0 : W) :
    ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
      ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (Submodule.Quotient.mk (p := twRel q j Γ(W, ⊤)) (Finsupp.single ξ 1)) =
        ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ) := by
  obtain ⟨k, hk, hc, e⟩ := exists_pow (W.Γevaluation w0).hom ζ ξ
  have hq : ((q : ℕ) : W.residueField w0) ≠ 0 := by
    have := ζ.2.1.map (W.Γevaluation w0).hom
    simpa using this.ne_zero
  obtain ⟨h1, h2⟩ := key_ring (W.Γevaluation w0).hom ξ.1 ζ.1 q k hq (prim_pow_eq_one ξ) (prim_pow_eq_one ζ) e
  refine ⟨W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b),
    (((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ) : ZMod q),
    (W.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) w0 trivial _).mp h1, ?_⟩
  have hs := h2 _ (Scheme.Γ.map (W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b)).ι.op).hom
    (isUnit_res _)
  refine (map_mk j _ ξ 1).trans ?_
  refine Eq.trans ?_ (LinearMap.map_smul _ _ _).symm
  refine Eq.trans ?_ (congrArg _ (map_mk j _ ζ 1).symm)
  exact mk_pow j _ _ k hk hc hs

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec

open Gen in
theorem LeafTwGen_of : LeafTwGen := by
  intro q _ j W ζ t w0
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q j Γ(W, ⊤)) t
  induction f using Finsupp.induction_linear with
  | zero =>
    refine ⟨⊤, 0, trivial, ?_⟩
    have hm : (Submodule.Quotient.mk 0 : (twF q j).obj Γ(W, ⊤)) = 0 := Submodule.Quotient.mk_zero _
    have h0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twCls j ζ = 0 := zero_smul _ _
    rw [hm, h0]
    exact rfl
  | add f g hf hg =>
    obtain ⟨O1, c1, h1, e1⟩ := hf
    obtain ⟨O2, c2, h2, e2⟩ := hg
    refine ⟨O1 ⊓ O2, c1 + c2, ⟨h1, h2⟩, ?_⟩
    have hm : (Submodule.Quotient.mk (f + g) : (twF q j).obj Γ(W, ⊤)) =
        (Submodule.Quotient.mk f : (twF q j).obj Γ(W, ⊤)) + (Submodule.Quotient.mk g : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_add _
    rw [hm]
    refine (LinearMap.map_add _ _ _).trans ?_
    rw [res_le j inf_le_left e1, res_le j inf_le_right e2]
    refine (LinearMap.map_add _ _ _).symm.trans ?_
    congr 1
    exact (add_smul _ _ _).symm
  | single ξ r =>
    obtain ⟨O, c, h, e⟩ := core j ζ ξ w0
    refine ⟨O, r.down * c, h, ?_⟩
    have hr : Finsupp.single ξ r = r • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hm : (Submodule.Quotient.mk (r • Finsupp.single ξ (1 : ULift.{1} (ZMod q))) : (twF q j).obj Γ(W, ⊤)) =
        r • (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_smul _ _ _
    rw [hr, hm]
    refine (LinearMap.map_smul _ _ _).trans ?_
    rw [e]
    refine (LinearMap.map_smul _ _ _).symm.trans ?_
    congr 1
    exact smul_smul _ _ _

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairHtpyPf

def LeafTwTensExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTensFactor : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
  ∀ ν : Pair I J K, ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T),
  τ.IsTensor → IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResHtpy : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∀ u u' : T ⟶ res _ (tw q k), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem secMap_id_f {R : Type} [CommRing R] (I : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (I.X s) U) :
    Sec.map ((𝟙 I : I ⟶ I).f s) x = x := by
  rw [HomologicalComplex.id_f]; rfl

theorem secMap_addx {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem secMap_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem hom_reindex {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (Hh : ∀ i j, T.X i ⟶ K.X j)
    (U : Scheme.{0}) (s t v n : ℤ) (hv : v + 1 = n) (hs : s + t = n) (hs' : s + t = v + 1)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (Hh (v + 1) v) (τ.mul U s t (v + 1) hs' a b) = Sec.map (Hh n v) (τ.mul U s t n hs a b) := by
  subst hv; rfl

theorem pairHtpy_of_homotopy {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (μ μ' : Pair I J K) (u u' : T ⟶ K)
    (hu : τ.Compat μ (𝟙 I) (𝟙 J) u) (hu' : τ.Compat μ' (𝟙 I) (𝟙 J) u') (H : Homotopy u u') :
    LateralTheory.E.LeafTwPairUniquePf.PairHtpy μ μ' := by
  refine ⟨fun U s t w hw => (τ.mul U s t (w + 1) hw).compr₂ (((H.hom (w + 1) w).hom.app (op U)).hom), ?_, ?_⟩
  · intro V U g s t w hw a b
    simp only [LinearMap.compr₂_apply]
    rw [← τ.nat g s t (w + 1) hw a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (τ.mul _ s t (w + 1) hw a b)) ((H.hom (w + 1) w).hom.naturality g.op)).symm
  · intro U s t w hw a b
    simp only [LinearMap.compr₂_apply]
    have e1 := hu U s t w hw a b
    have e2 := hu' U s t w hw a b
    rw [secMap_id_f, secMap_id_f] at e1 e2
    rw [← e1, ← e2]
    have hc := H.comm w
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel w (w + 1) by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (w - 1) w by simp)] at hc
    rw [hc, secMap_add, secMap_add, secMap_comp, secMap_comp]
    have e3 := hom_reindex τ H.hom U s t (w - 1) w (by omega) hw (by omega) a b
    have e3' : (ModuleCat.Hom.hom ((H.hom (w - 1 + 1) (w - 1)).hom.app (op U))) (τ.mul U s t (w - 1 + 1) (by omega) a b) =
        Sec.map (H.hom w (w - 1)) (τ.mul U s t w hw a b) := e3
    rw [e3']
    rw [τ.leibniz, secMap_addx, secMap_usmul]
    dsimp only [Sec.map]
    abel

end LateralTheory.E.LeafTwPairHtpyPf

open LateralTheory.E.LeafTwPairHtpyPf in
theorem LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of (hE : LeafTwTensExists) (hF : LeafTensFactor) (hR : LeafTwTensRes)
    (hH : LeafTwResHtpy) : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := by
  intro q _ i j μ μ' hμ hμ'
  obtain ⟨T, τ, hτ⟩ := hE q i j
  obtain ⟨u, hu⟩ := hF (ZMod q) τ hτ μ
  obtain ⟨u', hu'⟩ := hF (ZMod q) τ hτ μ'
  obtain ⟨H⟩ := hH q (i + j) _ (hR q i j τ hτ) u u' (fun U ζ => by
    have a1 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    have a2 := hu' U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [secMap_id_f, secMap_id_f] at a1 a2
    rw [a1, a2, hμ U ζ, hμ' U ζ])
  exact pairHtpy_of_homotopy τ μ μ' u u' hu hu' H
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwSecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwSecPf

def ρ {B : Type} [CommRing B] (U : Over (Spec (CommRingCat.of B))) : B →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ U.hom.appTop).hom

abbrev Pr (q : ℕ) (k : ℤ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Over.forget X).op ⋙ (Scheme.Γ ⋙ twF q k)

abbrev Cst (q : ℕ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Functor.const _).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))

def gen {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) (U : Over (Spec (CommRingCat.of B))) :
    (Pr q k _).obj (op U) :=
  Submodule.Quotient.mk (Finsupp.single (Prim.map (ρ U) ζ) 1)

theorem gen_map {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) {U V : Over (Spec (CommRingCat.of B))}
    (f : V ⟶ U) : ((Pr q k _).map f.op).hom (gen ζ k U) = gen ζ k V := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single _ _)) = _
  rw [Finsupp.mapDomain_single]
  have h : Prim.map (Scheme.Γ.map f.left.op).hom (Prim.map (ρ U) ζ) = Prim.map (ρ V) ζ := by
    apply Subtype.ext
    change (Scheme.Γ.map f.left.op).hom (ρ U ζ.1) = ρ V ζ.1
    simp only [ρ]
    rw [← Over.w f]
    first | rfl | simp [Scheme.Hom.comp_appTop] | simp
  exact congrArg (fun z => Submodule.Quotient.mk (p := twRel q k _) (Finsupp.single z (1 : ULift.{1} (ZMod q)))) h

def cmap {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) : Cst q _ ⟶ Pr q k (Spec (CommRingCat.of B)) where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (gen ζ k U.unop))
  naturality := by
    intro U V f
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k V.unop)) (1 : ULift.{1} (ZMod q)) =
      ((Pr q k _).map f).hom ((LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k U.unop)) (1 : ULift.{1} (ZMod q)))
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact (gen_map ζ k f.unop).symm

def LeafTwLB : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  IsIso ((presheafToSheaf (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (ModuleCat.{1} (ULift.{1} (ZMod q)))).map
    (cmap ζ k))

theorem LeafTwSec_of (h : LeafTwLB) : LateralTheory.E.LeafTwistPf.LeafTwSec := by
  intro q _ B _ ζ i j
  let K := (Over.forget (Spec (CommRingCat.of B))).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{1} (ULift.{1} (ZMod q))) (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) Scheme.etaleTopology
  haveI := h q B ζ i
  haveI := h q B ζ j
  let Φ := (K.app (Scheme.Γ ⋙ twF q i)).symm ≪≫ (asIso ((presheafToSheaf _ _).map (cmap ζ i))).symm ≪≫
    asIso ((presheafToSheaf _ _).map (cmap ζ j)) ≪≫ K.app (Scheme.Γ ⋙ twF q j)
  let Ψ := (sheafToPresheaf _ _).mapIso Φ
  refine ⟨fun U x => (Ψ.app (op (Over.mk x))).toLinearEquiv, ?_⟩
  intro V U g x s
  have := congrArg (fun f => f.hom s) (Ψ.hom.naturality (Over.homMk g : Over.mk (g ≫ x) ⟶ Over.mk x).op)
  exact this

def LeafTwSurj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

def LeafTwInj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallyInjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

theorem LeafTwLB_of (hI : LeafTwInj) (hS : LeafTwSurj) : LeafTwLB := by
  intro q _ B _ ζ k
  haveI := hI q B ζ k
  haveI := hS q B ζ k
  exact (GrothendieckTopology.W_iff _ _).1 (GrothendieckTopology.W_of_isLocallyBijective _ _)

theorem LeafTwSec_of' (hI : LeafTwInj) (hS : LeafTwSurj) : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LeafTwSec_of (LeafTwLB_of hI hS)

end LateralTheory.E.LeafTwSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitAWPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitAWPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) (U : Scheme.{0}) :
    Subsingleton (Sec ((res R F).X s) U) := by
  have hz : IsZero ((res R F).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h2 : IsZero (((res R F).X s).obj.obj (op U)) :=
    Functor.map_isZero ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op U)) hz
  exact ModuleCat.isZero_iff_subsingleton.mp h2

theorem sub_zero_self {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i : 3
    simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem main_gen (q : ℕ) [NeZero q] (E : Spc) (i j : ℤ) (hij : i = j)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q j)))
    (hU : ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneLoc α)
    (n k : ℤ) (hnk : n = k) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q j)) k, μ.IsAW (show 0 + n = k by omega) α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast hnk hij (CohomologyClass.mk β : Ht q E n i) := by
  subst hij hnk
  refine ⟨β, ?_, rfl⟩
  intro N w h U x
  have hmz : ∀ (s t w : ℤ) (h : s + t = w) (a : Sec ((res _ (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
      s < 0 → μ.mul U s t w h a b = 0 := by
    intro s t w h a b hs
    have := sec_sub (tw q 0) s hs U
    rw [Subsingleton.elim a 0]
    simp
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · subst h
    show _ = (n * ((0 : ℕ) : ℤ)).negOnePow • μ.mul U (-((0 : ℕ) : ℤ) + 0) (-((N - 0 : ℕ) : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 _ rfl U (x.sub 0 0 (by omega))) (ev β.1 (N - 0) _ rfl U (x.sub 0 (N - 0) (by omega)))
    have h1 : (n * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [h1, one_smul]
    show _ = μ.mul U 0 (-(N : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β.1 N _ rfl U (x.sub 0 N (by omega)))
    rw [sub_zero_self]
    exact (eq_of_heq (hU U _ _ (by omega) _ (ev β.1 N _ rfl U x) (hα U (x.sub 0 0 (by omega))))).symm
  · intro p _
    rw [hmz, smul_zero]
    simp
    omega

theorem LeafUnitAW_of : LeafUnitAW := by
  intro q _ E i μ hU α hα n β
  exact main_gen q E i (0 + i) (by ring) μ hU α hα n (0 + n) (by ring) β

end LateralTheory.E.LeafUnitAWPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem resGen_res' {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  have h1 : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) :
        (twF q i).obj Γ(U, ⊤)))
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    simp only [ModuleCat.hom_comp] at h
    refine h.symm.trans (congrArg (fun x => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom x) ?_)
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold resGen
  rw [← h1]
  exact congrArg (fun f => f.hom (twGen i ζ)) (((resι _ (tw q i)).hom.naturality g.op)).symm

def UnitPairLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → ν.mul U 0 t t (zero_add t) a b = b

theorem sec_eq_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  have hsh := (F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS).isSeparatedFor
  let fx : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  let fy : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have hxy : fx = fy := by
    refine hsh.ext (fun V g hg => ?_)
    change fx ≫ F.obj.map g.op = fy ≫ F.obj.map g.op
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (F.obj.map g.op).hom (fx.hom 1) = (F.obj.map g.op).hom (fy.hom 1)
    simpa [fx, fy] using hP V g hg
  have := congrArg (fun f => f.hom 1) hxy
  simpa [fx, fy] using this

def LeafUnitPairG : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U),
    ν.mul U 0 t t (zero_add t) (resGen 0 ζ) b = b

theorem unitPairLoc_of (h : LeafUnitPairG) : UnitPairLoc := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  refine ⟨ν, fun U t a b ha => sec_eq_of_loc _ _ _ ?_⟩
  obtain ⟨S, hS, hP⟩ := ha
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ, hζ⟩ := hP V g hg
  rw [ν.nat g 0 t t (zero_add t) a b, hζ, hν]

theorem leafUnitPair_of_loc (h : UnitPairLoc) : LeafUnitPair := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  have key : ∀ k (_ : i = k), ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)),
      ∀ U s t w (hw : s + t = w) a b, HEq (μ.mul U s t w hw a b) (ν.mul U s t w hw a b) := by
    rintro k rfl
    exact ⟨ν, fun _ _ _ _ _ _ _ => HEq.rfl⟩
  obtain ⟨μ, hμ⟩ := key (0 + i) (zero_add i).symm
  have gen : ∀ U t w w' (h1 : 0 + t = w) (h2 : 0 + t = w') (_ : w = w') a b,
      HEq (ν.mul U 0 t w h1 a b) (ν.mul U 0 t w' h2 a b) := by
    intro U t w w' h1 h2 e a b
    subst e
    rfl
  have hgen : ∀ k (_ : k = i) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), HEq (resGen k ζ) (resGen i ζ) := by
    rintro k rfl U ζ
    rfl
  refine ⟨μ, ?_, ?_⟩
  · intro U ζ
    have hloc : Loc U (fun V g => ∃ ζ' : Prim q Γ(V, ⊤), Sec.res g (resGen 0 ζ) = resGen 0 ζ') :=
      ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => ⟨_, resGen_res' 0 g ζ⟩⟩
    exact eq_of_heq ((hμ U 0 0 0 _ _ _).trans ((heq_of_eq (hν U 0 _ _ hloc)).trans (hgen _ (zero_add i) U ζ).symm))
  · intro U t w hw a b ha
    exact (hμ U 0 t w hw a b).trans ((gen U t w t hw (zero_add t) (by omega) a b).trans (heq_of_eq (hν U t a b ha)))

theorem LeafUnitPair_of (h : LeafUnitPairG) : LeafUnitPair := leafUnitPair_of_loc (unitPairLoc_of h)

end LateralTheory.E.LeafUnitPairPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.UnitExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneExistsPf

open LateralTheory.E.CupProductRingLaws

def LeafUnitSec : Prop := ∀ (q : ℕ) [NeZero q], ∃ one : ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Sec (tw q 0) U,
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : IsUnit (q : Γ(U, ⊤))) (hV : IsUnit (q : Γ(V, ⊤))),
    Sec.res g (one U hU) = one V hV) ∧
  ∀ (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (ζ : Prim q Γ(U, ⊤)), one U hU = twGen 0 ζ

def LeafCocycleOfSec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U),
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) →
  ∃ α : Cocycle ((chains R).obj E) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev α.1 0 0 (by simp) U x = Sec.map (resι R F) (s U ⟨x⟩)

theorem LeafOneExists_of (hU : LeafUnitSec) (hC : LeafCocycleOfSec) : LateralTheory.E.LeafOneSpecPf.LeafOneExists := by
  intro q _ E hE
  obtain ⟨one, hnat, hone⟩ := hU q
  obtain ⟨α, hα⟩ := hC (ZMod q) (tw q 0) E (fun U h => one U (hE U h))
    (fun V U g hU' hV' => hnat V U g _ _)
  refine ⟨α, fun U x ζ => ?_⟩
  rw [hα U x, hone U _ ζ]
  rfl

end LateralTheory.E.LeafOneExistsPf
end
end

