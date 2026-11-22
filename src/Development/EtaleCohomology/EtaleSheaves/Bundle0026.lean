import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.Bundle0012
import Development.EtaleCohomology.EtaleSheaves.Bundle0008
import Development.EtaleCohomology.EtaleSheaves.Bundle0015
import Development.EtaleCohomology.EtaleSheaves.Bundle0014

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable {R : Type} [CommRing R]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using h.symm

theorem map_map {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

def post {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (Sec.map (u.f w) _) = Sec.map (u.f w) _
    rw [res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) _) =
      Sec.map (u.f (w + 1)) _ + s.negOnePow • Sec.map (u.f (w + 1)) _
    rw [map_map, u.comm w (w + 1), ← map_map, μ.leibniz]
    simp only [Sec.map, map_add, map_zsmul_unit]

theorem post_mul {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : (post μ u).mul U s t w h a b = Sec.map (u.f w) (μ.mul U s t w h a b) := rfl

def LeafTwTensEx : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (T : Cx (ZMod q))
  (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor →
    IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResExt : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) (T : Cx (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∃ u : T ⟶ res _ (tw q k), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen k ζ

theorem LeafTwPairExists_of (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) (h3 : LeafTwResExt) :
    LateralTheory.E.CupProductRingLaws.LeafTwPairExists := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 q i j
  obtain ⟨u, hu⟩ := h3 q (i + j) T _ (h2 q i j T τ hτ)
  exact ⟨post τ u, fun U ζ => by rw [post_mul]; exact hu U ζ⟩

end LateralTheory.E.LeafTwPairExistsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPairUniquePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairUniquePf

def PairHtpy {R : Type} [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) : Prop :=
  ∃ h : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
      Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U,
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
        Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
          h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
          s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)

def LeafTwPairHtpy : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → PairHtpy μ μ'

def LeafHtpyAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K), PairHtpy μ μ' →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    CohomologyClass.mk γ = CohomologyClass.mk γ'

theorem cup_eq_of_aw {R : Type} [CommRing R] {I J K : Cx R} (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (μ μ' : Pair I J K)
    (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (hAW : ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
      CohomologyClass.mk γ = CohomologyClass.mk γ') :
    μ.cup E hk = μ'.cup E hk := by
  obtain ⟨ex, sp⟩ := hc R μ E hk
  obtain ⟨ex', sp'⟩ := hc R μ' E hk
  ext a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := ex α β
  obtain ⟨γ', hγ'⟩ := ex' α β
  rw [sp α β γ hγ, sp' α β γ' hγ']
  exact hAW α β γ γ' hγ hγ'

end LateralTheory.E.LeafTwPairUniquePf

open LateralTheory.E.LeafTwPairUniquePf in
theorem LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (hh : LeafTwPairHtpy)
    (ha : LeafHtpyAW) : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := by
  intro q _ i j μ μ' hμ hμ' E n m k hk
  exact cup_eq_of_aw hc μ μ' E hk (ha (ZMod q) μ μ' (hh q i j μ μ' hμ hμ') E hk)
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

def twCls {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (ζ : Prim q A) : (twF q j).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))

def LeafOfRingsLocSurj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (X : Scheme.{0}) (s : Sec (ofRings R M) X) (x : X), ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧
  ∃ t : M.obj Γ(U, ⊤), Sec.res w s = ofRings.sec M U t

def LeafOfRingsLocInj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (U : Scheme.{0}) (t : M.obj Γ(U, ⊤)), ofRings.sec M U t = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (v : V ⟶ U),
  Etale v ∧ u ∈ Set.range v ∧ (M.map (Scheme.Γ.map v.op)).hom t = 0

def LeafTwAdj : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (u : U), IsUnit (q : Γ(U, ⊤)) →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ Nonempty (Prim q Γ(W, ⊤))

def LeafTwGen : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (t : (twF q j).obj Γ(W, ⊤))
  (w0 : W), ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
    ((twF q j).map (Scheme.Γ.map O.ι.op)).hom t = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ)

def LeafTwFieldZ : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (K : CommRingCat.{0}), IsField K →
  ∀ (ζ : Prim q K) (c : ZMod q), ULift.up c • twCls j ζ = 0 → c = 0

def LeafTwPt : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (U : Scheme.{0}) (u : U) (t : (twF q j).obj Γ(U, ⊤))
  (V : Scheme.{0}) (g : V ⟶ U) (v : V), g v = u → ((twF q j).map (Scheme.Γ.map g.op)).hom t = 0 →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ ((twF q j).map (Scheme.Γ.map w.op)).hom t = 0

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (t : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U t) = ofRings.sec M V ((M.map (Scheme.Γ.map g.op)).hom t) := by
  have h := congrArg (fun f => f.hom t) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact h.symm

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res]

theorem sec_zero {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) :
    ofRings.sec M U 0 = 0 :=
  map_zero _

theorem goal_of (h1 : LeafOfRingsLocSurj) (h2 : LeafOfRingsLocInj) (h3 : LeafTwPt) : LateralTheory.E.E8.LeafTwSecKill := by
  intro q _ X Z _ ι _ hq j s hs x hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨U, w, hw, ⟨u, hu⟩, t, ht⟩ := h1 (ZMod q) (twF q j) X s (ι z)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := ι) u z hu
  have hP : ofRings.sec (twF q j) _ (((twF q j).map (Scheme.Γ.map (pullback.fst w ι).op)).hom t) = 0 := by
    rw [← sec_res, ← ht]
    have e2 : Sec.res (F := tw q j) (pullback.fst w ι) (Sec.res w s) =
        Sec.res (F := tw q j) (pullback.snd w ι) (Sec.res ι s) := by
      rw [← res_comp, ← res_comp, pullback.condition]
    exact e2.trans (by rw [hs]; exact map_zero _)
  obtain ⟨V, v, hv, ⟨v0, hv0⟩, hV⟩ := h2 (ZMod q) (twF q j) _ _ hP p
  have hV' : ((twF q j).map (Scheme.Γ.map (v ≫ pullback.fst w ι).op)).hom t = 0 := by
    rw [op_comp, Functor.map_comp, Functor.map_comp]
    exact hV
  obtain ⟨W, w', hw', hu', hW⟩ := h3 q j U u t V (v ≫ pullback.fst w ι) v0 (by simp [hv0, hp1]) hV'
  haveI := hw; haveI := hw'
  refine ⟨W, w' ≫ w, inferInstance, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hu'
    exact ⟨a, by simp [ha, hu]⟩
  · rw [res_comp]
    have e := sec_res (twF q j) w' t
    rw [hW] at e
    exact (congrArg (Sec.res w') ht).trans (e.trans (sec_zero _ _))

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwistPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwistPf

def LeafLoc : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R)
  (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) →
  ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

def LeafTwSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Prim q B → ∀ i j : ℤ,
  ∃ e : ∀ U : Scheme.{0}, (U ⟶ Spec (CommRingCat.of B)) → (Sec (tw q i) U ≃ₗ[ULift.{1} (ZMod q)] Sec (tw q j) U),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ Spec (CommRingCat.of B)) (s : Sec (tw q i) U),
      e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)

theorem LeafTwist_of (hL : LeafLoc) (hT : LeafTwSec) : LateralTheory.E.LeafKumCut.LeafTwist := by
  intro hy q _ B _ hP n i j
  obtain ⟨ζ⟩ := hP
  obtain ⟨e, he⟩ := hT q B ζ i j
  exact hL hy (ZMod q) (Spec (CommRingCat.of B)) (tw q i) (tw q j) e he n

end LateralTheory.E.LeafTwistPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfB
section
namespace LateralTheory.E.E4

theorem mem_range_of_isIntegral {k B : Type} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] {x : B} (hx : IsIntegral k x) : x ∈ Set.range (algebraMap k B) := by
  have h : (minpoly k x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx)
  have hm : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic hx
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul, map_add,
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hm
  exact ⟨-(minpoly k x).coeff 0, by rw [map_neg]; exact hm.symm⟩

theorem fg_subgroup_mult (n : ℕ) (H : Subgroup (Multiplicative (Fin n → ℤ))) : Group.FG H := by
  have : IsNoetherian ℤ (Additive (Multiplicative (Fin n → ℤ))) :=
    isNoetherian_of_linearEquiv (AddEquiv.additiveMultiplicative (Fin n → ℤ)).symm.toIntLinearEquiv
  rw [Group.fg_iff_subgroup_fg, Subgroup.fg_iff_add_fg]
  have := IsNoetherian.noetherian (R := ℤ) H.toAddSubgroup.toIntSubmodule
  exact (Submodule.fg_iff_addSubgroup_fg _).1 this

def LeafUnitsOrd : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B],
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsFG_of (h : LeafUnitsOrd) : LeafUnitsFG := by
  intro k B _ _ _ _ _ _
  obtain ⟨n, φ, hφ⟩ := h k B
  have hker : φ.ker ≤ (Units.map (algebraMap k B).toMonoidHom).range := by
    intro u hu
    obtain ⟨a, ha⟩ := mem_range_of_isIntegral (hφ u hu)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact u.ne_zero ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩
  have : Group.FG φ.range := fg_subgroup_mult n _
  have : Group.FG (Bˣ ⧸ φ.ker) :=
    Group.fg_of_surjective (f := ((QuotientGroup.quotientKerEquivRange φ).symm : φ.range →* Bˣ ⧸ φ.ker))
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map φ.ker (Units.map (algebraMap k B).toMonoidHom).range (MonoidHom.id _) hker) ?_
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk u, rfl⟩

def LeafUnitsOrdCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem isIntegral_of_isField {k B : Type} [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (hB : IsField B) (x : B) : IsIntegral k x := by
  let _ := hB.toField
  have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  exact Algebra.IsIntegral.isIntegral x

theorem LeafUnitsOrd_of (h : LeafUnitsOrdCurve) : LeafUnitsOrd := by
  intro k B _ _ _ _ _ _
  by_cases hB : IsField B
  · exact ⟨0, 1, fun u _ => isIntegral_of_isField hB _⟩
  · exact h k B hB

theorem LeafUnitsFG_of_curve (h : LeafUnitsOrdCurve) : LeafUnitsFG := LeafUnitsFG_of (LeafUnitsOrd_of h)

def LeafNoetherCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ g : Polynomial k →ₐ[k] B, Function.Injective g ∧ g.Finite

def LeafOrdAtInfinity : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsOrdCurve_of (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsOrdCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨g, hg, hf⟩ := hN k B hB
  exact hV k B g hg hf

theorem LeafUnitsFG_of_leaves (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_curve (LeafUnitsOrdCurve_of hN hV)

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LevelIdentPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LevelIdentPf

def FreeSingleHomotopyEquivDiscreteChains : Prop := ∀ (R : Type) [CommRing R], ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)),
  (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧
  ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
    (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp _ x _) = CohomologyClass.mk (zcomp _ x _)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, n.negOnePow • (Cochain.ofHomotopy h).comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (by omega) 0 (n + 1) n (by omega) (by omega) (by omega), δ_ofHomotopy]
  simp [zcomp, Cocycle.δ_eq_zero, Cochain.sub_comp, smul_smul, Int.units_mul_self]

theorem cpull_iso_bij {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, cpull_homotopy e.homotopyInvHomId, cpull_id]
  · rw [← cpull_comp, cpull_homotopy e.homotopyHomInvId, cpull_id]

theorem sq_iff {A B C D : Type*} {a : B → D} {b : A → B} {c : C → D} {d : A → C}
    (w : ∀ x, a (b x) = c (d x)) (ha : Function.Bijective a) (hd : Function.Bijective d) :
    (Function.Bijective b ↔ Function.Bijective c) ∧ (Function.Injective b ↔ Function.Injective c) := by
  have w' : a ∘ b = c ∘ d := funext w
  obtain ⟨d', hd1, hd2⟩ := Function.bijective_iff_has_inverse.1 hd
  have hc : c = a ∘ b ∘ d' := by
    funext y; simp only [Function.comp_apply, w, hd2 y]
  have hd'b : Function.Bijective d' := Function.bijective_iff_has_inverse.2 ⟨d, hd2, hd1⟩
  refine ⟨⟨fun hb => hc ▸ ha.comp (hb.comp hd'b), fun hc' => ?_⟩, ⟨fun hb => hc ▸ ha.1.comp (hb.comp hd'b.1), fun hc' => ?_⟩⟩
  · have : a ∘ b = c ∘ d := w'
    have hab : Function.Bijective (a ∘ b) := this ▸ hc'.comp hd
    obtain ⟨a', ha1, ha2⟩ := Function.bijective_iff_has_inverse.1 ha
    have : b = a' ∘ (a ∘ b) := by funext x; simp [ha1 (b x)]
    rw [this]; exact (Function.bijective_iff_has_inverse.2 ⟨a, ha2, ha1⟩).comp hab
  · intro x y hxy
    apply hd.1; apply hc'
    rw [← w, ← w, hxy]

theorem chains_f {E E' : Spc} (f : E ⟶ E') (n : ℕ) : ((chains R).map f).f (-(n : ℤ)) =
    (chainsXIso R E n).hom ≫ (free R).map (f.app (op (SimplexCategory.mk n))) ≫ (chainsXIso R E' n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem cpull_isoHom_bij {K L : Cx R} (i : K ≅ L) (I : Cx R) (n : ℤ) : Function.Bijective (cpull i.hom I n) :=
  cpull_iso_bij (HomotopyEquiv.ofIso i) I n

theorem pull_eq {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R f F n x = cpull ((chains R).map f) (res R F) n x := rfl

theorem LevelIdent_of (hS : FreeSingleHomotopyEquivDiscreteChains) : LateralTheory.E.DescStepPf.LevelIdent := by
  intro R _ F E E' f p j
  obtain ⟨e, -, he⟩ := hS R
  let S := CochainComplex.singleFunctor (Shv R) 0
  let g := f.app (op (SimplexCategory.mk p))
  have sq1 : S.map (((chains R).map f).f (-(p : ℤ))) ≫ S.map (chainsXIso R E' p).hom =
      S.map (chainsXIso R E p).hom ≫ S.map ((free R).map g) := by
    rw [← S.map_comp, ← S.map_comp, chains_f]; simp [g]
  have w1 : ∀ x, cpull (S.map (chainsXIso R E p).hom) (res R F) j (cpull (S.map ((free R).map g)) (res R F) j x) =
      cpull (S.map (((chains R).map f).f (-(p : ℤ)))) (res R F) j (cpull (S.map (chainsXIso R E' p).hom) (res R F) j x) := by
    intro x; rw [← cpull_comp, ← cpull_comp, sq1]
  have w2 : ∀ x, cpull (e (E.obj (op (SimplexCategory.mk p)))).hom (res R F) j (pull R (disc.map g) F j x) =
      cpull (S.map ((free R).map g)) (res R F) j (cpull (e (E'.obj (op (SimplexCategory.mk p)))).hom (res R F) j x) := by
    intro x; rw [pull_eq, ← cpull_comp, ← cpull_comp, he g]
  obtain ⟨b1, i1⟩ := sq_iff w1 (cpull_isoHom_bij (S.mapIso (chainsXIso R E p)) _ _)
    (cpull_isoHom_bij (S.mapIso (chainsXIso R E' p)) _ _)
  obtain ⟨b2, i2⟩ := sq_iff w2 (cpull_iso_bij _ _ _) (cpull_iso_bij _ _ _)
  exact ⟨b2.trans b1, i2.trans i1⟩

end LateralTheory.E.LevelIdentPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocEtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.LocEtPf

lemma et_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    Et (X.presheaf.map (homOfLE h).op) := by
  have := (𝟙 X : X ⟶ X).etale_appLE hU hV h
  show (X.presheaf.map (homOfLE h).op).hom.Etale
  convert this using 2
  rfl

theorem LocEt_of : LocEt := by
  intro T X p _ x
  obtain ⟨_, _, V0, hV0, hx0, -, -⟩ := Smooth.exists_isStandardSmooth p x
  have hf : (p.appLE ⊤ V0 (by simp)).hom.Smooth := p.smooth_appLE (isAffineOpen_top _) hV0 _
  have hloc := (RingHom.Smooth.locally_isStandardSmooth hf).span_eq_top
  have hcov := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top V0 _ hloc
  have hx1 : x ∈ (⨆ i ∈ {g : Γ(X, V0) | ((algebraMap Γ(X, V0) (Localization.Away g)).comp
      (p.appLE ⊤ V0 (by simp)).hom).IsStandardSmooth}, X.basicOpen i) := by rw [hcov]; exact hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx1
  obtain ⟨t, ht, hxt⟩ := hx1
  have hB := hV0.basicOpen t
  let := hV0.isLocalization_basicOpen t
  let e : Localization.Away t ≃ₐ[Γ(X, V0)] Γ(X, X.basicOpen t) :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  have hs : (gam p (X.basicOpen t)).hom.IsStandardSmooth := by
    have h1 := (RingHom.isStandardSmooth_respectsIso.1 _ e.toRingEquiv ht)
    have h2 := RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv.symm h1
    have hgam : gam p (X.basicOpen t) = (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V0 (by simp) ≫
        X.presheaf.map (homOfLE (X.basicOpen_le t)).op := by
      simp only [gam]
      congr 1
      exact (Scheme.Hom.appLE_map ..).symm
    have halg : algebraMap Γ(X, V0) Γ(X, X.basicOpen t) = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom := rfl
    rw [hgam]
    convert h2 using 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, halg]
    rfl
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  refine ⟨X.basicOpen t, n, hxt, fun V hV hVU => ?_⟩
  refine ⟨CommRingCat.ofHom g ≫ X.presheaf.map (homOfLE hVU).op, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ hg (et_res hB hV hVU)
  · ext1
    rw [← Category.assoc]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [hgC]
    simp only [gam, Scheme.Hom.appLE, ← CommRingCat.hom_comp, Category.assoc, ← Functor.map_comp]
    rfl

end LateralTheory.E.LocEtPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocalDescent
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescLocPf

def LocPts (q : ℕ) (i : ℤ) {A Y D : CommRingCat.{0}} (φ : A ⟶ Y) (d : A ⟶ D) : Prop :=
  ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)

def CokLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)

def KerLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → LocPts q i φ c →
    ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
    ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  Function.Injective (pull _ (sch.map (Spec.map φ')) (tw q i) n)

theorem DescLoc_of (hC : CokLoc) (hK : KerLoc) : LateralTheory.E.StalkCut.DescLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD hpts Y' w φ' hpo
  exact ⟨hC hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo,
    hK hH q i n φ hq P hpush het hlow (fun C c hC' hpC => hC hH q i n φ hq P hpush het hlow C c hC' hpC) D d hD hpts Y' w φ' hpo⟩

end LateralTheory.E.DescLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SepTensorPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SepTensorPf

theorem SepTensor_of : LateralTheory.E.SHTensorPf.SepTensor := by
  intro A X B Z x b u v hp _ hX _ hb _ hZ
  obtain ⟨_, hXs⟩ := hX
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  let f : X →+* IsLocalRing.ResidueField Z := (IsLocalRing.residue Z).comp u.hom
  have hf : f.IsIntegral := RingHom.IsIntegral.trans u.hom (IsLocalRing.residue Z) hu
    (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective)
  let _ : Algebra X (IsLocalRing.ResidueField Z) := f.toAlgebra
  have : Algebra.IsIntegral X (IsLocalRing.ResidueField Z) := ⟨hf⟩
  have : Algebra.IsIntegral (IsLocalRing.ResidueField X) (IsLocalRing.ResidueField Z) :=
    Algebra.IsIntegral.tower_top X
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField X)

end LateralTheory.E.SepTensorPf
end
end

