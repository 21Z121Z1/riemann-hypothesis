import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

-- bundled from Development.EtaleCohomology.EtaleTrace.LCycleCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.LCycleCut

def Dbl {X : Scheme.{0}} (U : X.Opens) : Spc := pushout (sch.map U.ι) (sch.map U.ι)

def i1 {X : Scheme.{0}} (U : X.Opens) : sch.obj X ⟶ Dbl U := pushout.inl _ _

def i2 {X : Scheme.{0}} (U : X.Opens) : sch.obj X ⟶ Dbl U := pushout.inr _ _

def fold {X : Scheme.{0}} (U : X.Opens) : Dbl U ⟶ sch.obj X := pushout.desc (𝟙 _) (𝟙 _) rfl

def dmap {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) : Dbl U' ⟶ Dbl U :=
  pushout.map _ _ _ _ (sch.map f) (sch.map f) (sch.map (f.resLE U U' h))
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])

def off {Z X : Scheme.{0}} (ι : Z ⟶ X) : X.Opens := ⟨interior (Set.range ι)ᶜ, isOpen_interior⟩

structure SmPair {k : Type} [Field k] (d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X) : Prop where
  closed : IsClosedImmersion ι
  qc : QuasiCompact p
  sep : IsSeparated p
  big : SmoothOfRelativeDimension (e + d) p
  small : SmoothOfRelativeDimension e (ι ≫ p)

abbrev TFam (l : ℕ) (k : Type) [Field k] (w : ℕ → ℤ) : Type 1 :=
  ∀ (j d : ℕ) {X : Scheme.{0}} (_ : X ⟶ S k) (U : X.Opens), Ht (l ^ j) (Dbl U) (2 * d) (w d)

structure IsThom {l : ℕ} {k : Type} [Field k] {w : ℕ → ℤ} (τ : TFam l k w) : Prop where
  supp : ∀ (j d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι →
    pull _ (i2 (off ι)) _ _ (τ j d p (off ι)) = 0
  nat : ∀ (j d e' e : ℕ) {Z' X' Z X : Scheme.{0}} (p' : X' ⟶ S k) (ι' : Z' ⟶ X') (p : X ⟶ S k) (ι : Z ⟶ X),
    SmPair d e' p' ι' → SmPair d e p ι → ∀ (f : X' ⟶ X) (g : Z' ⟶ Z), f ≫ p = p' → IsPullback ι' g f ι →
    ∀ h : off ι' ≤ f ⁻¹ᵁ off ι, pull _ (dmap f _ _ h) _ _ (τ j d p (off ι)) = τ j d p' (off ι')
  gen : ∀ (j d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (y : Pt p), SmPair d 0 p y.1 →
    ∀ a : Ht (l ^ j) (Dbl (off y.1)) (2 * d) (w d), pull _ (i2 (off y.1)) _ _ a = 0 → ∃ r : ℕ, a = r • τ j d p (off y.1)
  red : ∀ (j d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι →
    red (l ^ (j + 1)) (l ^ j) _ _ _ (τ (j + 1) d p (off ι)) = τ j d p (off ι)

def lev {l : ℕ} {k : Type} [Field k] (τ : TFam l k fun _ => 0) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (U : X.Opens) (j : ℕ) :
    Ht (l ^ j) (sch.obj X) (2 * d) 0 := pull _ (i1 U) _ _ (τ j d p U)

open Classical in

def cyc {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (τ : TFam l k fun _ => 0) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k)
    (U : X.Opens) : V l X (2 * d) :=
  if h : (lev τ d p U : ∀ j, HtL l j (sch.obj X) (2 * d) 0) ∈ HlSub l (sch.obj X) (2 * d) 0 then (1 : ℚ_[l]) ⊗ₜ ⟨_, h⟩ else 0

def LDbl : Prop := Base → ∀ (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} (U : X.Opens),
  (∀ (n : ℤ) (x : H R (sch.obj X) F n), pull R (sch.map U.ι) F n x = 0 →
    ∃ a : H R (Dbl U) F n, pull R (i1 U) F n a = x ∧ pull R (i2 U) F n a = 0) ∧
  ∀ m : ℤ, Function.Surjective (pull R (sch.map U.ι) F m) →
    ∀ a : H R (Dbl U) F (m + 1), pull R (i1 U) F _ a = 0 → pull R (i2 U) F _ a = 0 → a = 0

def LExc : Prop := Base → ∀ (R : Type) [CommRing R] (F : Shv R) {Z X' X : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X),
  Etale f → IsClosedImmersion ι → IsPullback ι' (𝟙 Z) f ι → ∀ (h : off ι' ≤ f ⁻¹ᵁ off ι) (n : ℤ),
  (∀ a : H R (Dbl (off ι)) F n, pull R (i2 _) F n a = 0 → pull R (dmap f _ _ h) F n a = 0 → a = 0) ∧
  ∀ a' : H R (Dbl (off ι')) F n, pull R (i2 _) F n a' = 0 →
    ∃ a : H R (Dbl (off ι)) F n, pull R (i2 _) F n a = 0 ∧ pull R (dmap f _ _ h) F n a = a'

def LDisj : Prop := Base → ∀ (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} (U : X.Opens) (I : Type) [Finite I]
  (W : I → X.Opens), U ⊔ iSup W = ⊤ → (∀ i j, i ≠ j → W i ⊓ W j ≤ U) → ∀ (n : ℤ) (a : H R (Dbl U) F n),
  pull R (i2 U) F n a = 0 → (∀ i, pull R (dmap (W i).ι ((W i).ι ⁻¹ᵁ U) U le_rfl) F n a = 0) → a = 0

def LSemi : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (d e : ℕ) {Z X : Scheme.{0}}
  (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι → ∀ n i : ℤ, n < 2 * d →
  ∀ a : Ht q (Dbl (off ι)) n i, pull _ (i2 _) _ _ a = 0 → a = 0

def LSupp : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ {Z X : Scheme.{0}}
  (p : X ⟶ S k) (ι : Z ⟶ X), IsClosedImmersion ι → QuasiCompact p → IsSeparated p → LocallyOfFiniteType p →
  ∀ (n m i j : ℤ) (a : Ht q (Dbl (off ι)) n i) (b : Ht q (sch.obj X) m j), pull _ (i2 _) _ _ a = 0 →
  pull _ (sch.map ι) _ _ b = 0 → cup q (E := sch.obj X) (pull _ (i1 _) _ _ a) b = 0

def LThom : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∃ τ : TFam l k fun d => d, IsThom τ

def LUnit : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ i : ℤ,
  ∃ (u : Ht q (sch.obj (S k)) 0 i) (v : Ht q (sch.obj (S k)) 0 (-i)),
    (cup q u v).cast (add_zero 0) (add_neg_cancel i) = one q (sch.obj (S k))

def LUntwist : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ τ : TFam l k fun d => d, IsThom τ → ∃ τ' : TFam l k fun _ => 0, IsThom τ'

def LNat : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (τ : TFam l k fun _ => 0), IsThom τ →
  ∀ (d e' e : ℕ) {Z' X' Z X : Scheme.{0}} (p' : X' ⟶ S k) (ι' : Z' ⟶ X') (p : X ⟶ S k) (ι : Z ⟶ X),
  SmPair d e' p' ι' → SmPair d e p ι → ∀ (f : X' ⟶ X) (g : Z' ⟶ Z), f ≫ p = p' → IsPullback ι' g f ι →
  pb l f _ (cyc τ d p (off ι)) = cyc τ d p' (off ι')

def LKill : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ τ : TFam l k fun _ => 0, IsThom τ →
  ∀ (d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι → ∀ (m : ℤ) (β : V l X m),
  pb l ι m β = 0 → cupV l X rfl (cyc τ d p (off ι)) β = 0

def LPts : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {Z : Scheme.{0}} (r : Z ⟶ S k), Etale r →
  (∀ t : Pt r, IsOpenImmersion t.1) ∧ ∀ z : Z, ∃ t : Pt r, z ∈ Set.range t.1

def LAdd : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (τ : TFam l k fun _ => 0), IsThom τ →
  ∀ (d : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d 0 p ι → ∀ s : Finset (Pt p),
  (∀ y, y ∈ s ↔ ∃ t : S k ⟶ Z, t ≫ ι = y.1) → cyc τ d p (off ι) = ∑ y ∈ s, cyc τ d p (off y.1)

def LSpan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (τ : TFam l k fun _ => 0), IsThom τ →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (y : Pt p), SmPair d 0 p y.1 →
  ∀ z : V l X (2 * d), pb l (off y.1).ι _ z = 0 → ∃ r : ℚ_[l], z = r • cyc τ d p (off y.1)

def LGeom : Prop := ∀ (k : Type) [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p →
  SmPair d d (pullback.fst p p ≫ p) (pullback.diagonal p) ∧
  (∀ y : Pt p, SmPair d 0 p y.1 ∧ ∀ h, IsPullback y.1 y.1 (pullback.lift (𝟙 X) (p ≫ y.1) h) (pullback.diagonal p)) ∧
  ∀ {Y : Scheme.{0}} (q : Y ⟶ S k), SP d q → ∀ (c a : Y ⟶ X), c ≫ p = q → Etale (equalizer.ι c a ≫ q) → ∀ h,
    SmPair d 0 q (equalizer.ι c a) ∧
    IsPullback (equalizer.ι c a) (equalizer.ι c a ≫ c) (pullback.lift c a h) (pullback.diagonal p)

theorem pb_comp (l : ℕ) [Fact l.Prime] {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l g n (pb l f n x) = pb l (g ≫ f) n x := by
  simp only [pb, pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp, LinearMap.comp_apply]

theorem goal_of (_h1 : LDbl) (_h2 : LExc) (_h3 : LDisj) (_h4 : LSemi) (_h5 : LSupp) (hT : LThom) (_h7 : LUnit) (hU : LUntwist)
    (hN : LNat) (hK : LKill) (_h11 : LPts) (hA : LAdd) (hS : LSpan) (hG : LGeom) : LCycle := by
  intro B l _ k _ _ hl
  obtain ⟨τ₀, h₀⟩ := hT B l k hl
  obtain ⟨τ, hτ⟩ := hU B l k hl τ₀ h₀
  let δ : Fam l k := fun d _ p => cyc τ d (pullback.fst p p ≫ p) (off (pullback.diagonal p))
  have hcl : ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ y : Pt p, δ.cl d y = cyc τ d p (off y.1) := by
    intro d X p hp y
    obtain ⟨hd, hy, -⟩ := hG k d p hp
    exact hN l k τ hτ d 0 d p y.1 _ _ (hy y).1 hd _ y.1 (by rw [pullback.lift_fst_assoc, Category.id_comp]) ((hy y).2 _)
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro d X p hp m β
    have h := hK B l k hl τ hτ d d _ _ (hG k d p hp).1 m (pb l (pullback.fst p p) m β - pb l (pullback.snd p p) m β)
      (by rw [map_sub, pb_comp, pb_comp, pullback.diagonal_fst, pullback.diagonal_snd, sub_self])
    rw [map_sub, sub_eq_zero] at h
    exact h
  · intro d Y X q p hq hp c a hc ha he s hs
    obtain ⟨hd, -, hE⟩ := hG k d p hp
    obtain ⟨hE1, hE2⟩ := hE q hq c a hc he (hc.trans ha.symm)
    have h1 : δ.corr d c a hc ha = cyc τ d q (off (equalizer.ι c a)) :=
      hN l k τ hτ d 0 d q _ _ _ hE1 hd _ _ (by rw [pullback.lift_fst_assoc, hc]) hE2
    rw [h1, hA B l k τ hτ d q _ hE1 s fun y => (hs y).trans
      ⟨fun h => ⟨equalizer.lift y.1 h, equalizer.lift_ι _ _⟩, fun ⟨t, ht⟩ => by
        rw [← ht, Category.assoc, Category.assoc, equalizer.condition]⟩]
    exact Finset.sum_congr rfl fun y _ => (hcl d q hq y).symm
  · intro d X p hp y U hU' z hz
    have hy := ((hG k d p hp).2.1 y).1
    have : U = off y.1 := by
      ext1
      change (U : Set X) = interior _
      rw [← hU', U.isOpen.interior_eq]
    subst this
    rw [hcl d p hp y]
    exact hS B l k τ hτ d p y hy z hz

end LateralTheory.EtaleTrace.LCycleCut

end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LTransferCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.Tr

def Splits {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) : Prop :=
  ∃ hs : ∀ j, s j ≫ a = x, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x)

section
variable (R : Type) [CommRing R]

abbrev fr (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

abbrev frMap {Y X : Scheme.{0}} (f : Y ⟶ X) : fr R Y ⟶ fr R X := (free R).map (yoneda.map f)

abbrev gen {U X : Scheme.{0}} (x : U ⟶ X) : Sec (fr R X) U := freeGen R (yoneda.obj X) U x

def IsTr {Y X : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
    Sec.map τ (gen R x) = ∑ j, gen R (s j)

variable {R}

def simp0 {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X) ⟶
      ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj Y) where
  app _ := τ
  naturality _ _ _ := by
    change (free R).map (𝟙 _) ≫ τ = τ ≫ (free R).map (𝟙 _)
    simp

def chMap {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) : (chains R).obj (sch.obj X) ⟶ (chains R).obj (sch.obj Y) :=
  (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 τ))

def trH {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) (F : Shv R) (n : ℤ) : H R (sch.obj Y) F n →+ H R (sch.obj X) F n :=
  HK.pull R (chMap τ) F n

theorem trH_smul {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) (F : Shv R) (n : ℤ) (r : R) (z : H R (sch.obj Y) F n) :
    trH τ F n (r • z) = r • trH τ F n z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_smul _ _ _ (zero_add n)))

theorem trH_add {X Y : Scheme.{0}} (σ τ : fr R X ⟶ fr R Y) (F : Shv R) (n : ℤ)
    (z : H R (sch.obj Y) F n) : trH (σ + τ) F n z = trH σ F n z + trH τ F n z := by
  have h : chMap (σ + τ) = chMap σ + chMap τ := by
    have : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 (σ + τ)) =
      (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 σ) +
      (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 τ) := by
      ext n : 1
      rfl
    exact (congrArg (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map this).trans (Functor.map_add _)
  obtain ⟨z, rfl⟩ := z.mk_surjective
  unfold trH
  rw [h]
  refine Eq.trans ?_ (CohomologyClass.mk_add _ _)
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

def trA {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) (z : H R (sch.obj Y) F n) : (fr R X ⟶ fr R Y) →+ H R (sch.obj X) F n :=
  AddMonoidHom.mk' (fun τ => trH τ F n z) (fun σ τ => trH_add σ τ F n z)

end

def LSpl : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
  (∀ (U : Scheme.{0}) (w : U ⟶ W), Splits a (w ≫ x) m (fun j => w ≫ s j)) ∧
  (∀ y : W ⟶ Y, y ≫ a = x → ∀ t : W, ∃ (O : W.Opens) (j : Fin m), t ∈ O ∧ O.ι ≫ y = O.ι ≫ s j) ∧
  (Nonempty W → Function.Injective s)

def LRank : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∀ (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s → ∀ w : W, a.finrank (x w) = m

def LPeel : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ σ : X ⟶ Y, σ ≫ a = 𝟙 X →
  ∃ (O : Scheme.{0}) (i : O ⟶ Y), IsFinite (i ≫ a) ∧ Etale (i ≫ a) ∧ (∀ t, a.finrank t = (i ≫ a).finrank t + 1) ∧
    ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ O)), Splits (i ≫ a) x m s →
      Splits a x (m + 1) (Fin.cons (x ≫ σ) fun j => s j ≫ i)

def LMul : Prop := ∀ {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (a : Y ⟶ X), IsFinite g → Etale g → IsFinite a → Etale a →
  ∀ N : ℕ, (∀ y, g.finrank y = N) → ∀ t, (g ≫ a).finrank t = N * a.finrank t

def LFrame : Prop := ∀ (m : ℕ) {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → (∀ t, a.finrank t = m) →
  ∃ (W : Scheme.{0}) (f : W ⟶ X) (N : ℕ) (s : Fin m → (W ⟶ Y)), IsFinite f ∧ Etale f ∧ 0 < N ∧ (∀ t, f.finrank t = N) ∧
    Splits a f m s

def LPiece : Prop := ∀ (m : ℕ) {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ (W : Scheme.{0}) (f : W ⟶ X) (N : ℕ) (s : Fin m → (W ⟶ Y)), IsFinite f ∧ Etale f ∧ 0 < N ∧
    (∀ t, f.finrank t = if a.finrank t = m then N else 0) ∧ Splits a f m s

def LLoc : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (W : Scheme.{0}) (x : W ⟶ X) (t : W),
  ∃ (U : Scheme.{0}) (g : U ⟶ W) (m : ℕ) (s : Fin m → (U ⟶ Y)), Etale g ∧ t ∈ Set.range g ∧ Splits a (g ≫ x) m s

def LSum : Prop := ∀ (R : Type) [CommRing R] {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m m' : ℕ) (s : Fin m → (W ⟶ Y))
  (s' : Fin m' → (W ⟶ Y)), Splits a x m s → Splits a x m' s' → ∑ j, gen R (s j) = ∑ j, gen R (s' j)

def LTau : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ τ : fr R X ⟶ fr R Y, IsTr R a τ

def LSplit : Prop := ∀ (R : Type) [CommRing R] {Y X W : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y), IsTr R a τ →
  ∀ (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s → frMap R x ≫ τ = ∑ j, frMap R (s j)

def LDeg : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} {ι : Type} [Fintype ι] (W : ι → Scheme.{0}) (f : ∀ i, W i ⟶ X)
  (τ : ∀ i, fr R X ⟶ fr R (W i)) (c : ι → ℕ) (N : ℕ), (∀ i, IsFinite (f i) ∧ Etale (f i) ∧ IsTr R (f i) (τ i)) →
  (∀ t, ∑ i, c i * (f i).finrank t = N) → ∑ i, c i • (τ i ≫ frMap R (f i)) = N • 𝟙 (fr R X)

def LImg : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
  (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n,
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)

def LRed : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R) (ρ : SemiMap (res S F) (res R G))
  {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (σ : fr S X ⟶ fr S Y) (τ : fr R X ⟶ fr R Y),
  IsTr S a σ → IsTr R a τ → ∀ (n : ℤ) (z : H S (sch.obj Y) F n),
  ρ.op.app (sch.obj X) n (trH σ F n z) = trH τ G n (ρ.op.app (sch.obj Y) n z)

section Glue
variable (l : ℕ) [Fact l.Prime]

def trL (hR : LRed) {Y X : Scheme.{0}} (a : Y ⟶ X) (h1 : IsFinite a) (h2 : Etale a)
    (τ : ∀ j, fr (ZMod (l ^ j)) X ⟶ fr (ZMod (l ^ j)) Y) (hτ : ∀ j, IsTr _ a (τ j)) (n : ℤ) :
    Hl l (sch.obj Y) n 0 →ₗ[ℤ_[l]] Hl l (sch.obj X) n 0 where
  toFun z := ⟨fun j => trH (τ j) _ n (z.1 j), fun j =>
    (hR _ _ _ _ (redMap (l ^ (j + 1)) (l ^ j) 0) a h1 h2 _ _ (hτ (j + 1)) (hτ j) n _).trans (congrArg _ (z.2 j))⟩
  map_add' x y := Subtype.ext (funext fun j => map_add (trH (τ j) _ n) (x.1 j) (y.1 j))
  map_smul' r x := Subtype.ext (funext fun j => trH_smul (τ j) _ n (PadicInt.toZModPow j r) (x.1 j))

def lev (E : Spc) (n : ℤ) (j : ℕ) : Hl l E n 0 →+ Ht (l ^ j) E n 0 where
  toFun z := z.1 j
  map_zero' := rfl
  map_add' _ _ := rfl

end Glue

end LateralTheory.EtaleTrace.Tr

end
end

