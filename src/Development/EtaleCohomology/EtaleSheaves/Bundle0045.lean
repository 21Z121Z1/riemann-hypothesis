import Development.EtaleCohomology.EtaleSheaves.Bundle0040
import Development.EtaleCohomology.EtaleSheaves.Bundle0022
import Development.EtaleCohomology.EtaleSheaves.Bundle0039
import Development.EtaleCohomology.EtaleSheaves.Bundle0036
import Development.EtaleCohomology.EtaleSheaves.Bundle0041
import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Development.EtaleCohomology.EtaleSheaves.Bundle0028
import Development.EtaleCohomology.EtaleSheaves.LeafOneHighPf
import Development.EtaleCohomology.TateTwists.Bundle0009
import Development.EtaleCohomology.TateTwists.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0023

-- bundled from Development.EtaleCohomology.EtaleSheaves.FiltPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces

namespace LateralTheory.E.FiltPf

namespace Tri

open Pretriangulated
universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]

def RelY (Y : ℤ → D) (n : ℤ) {A B : D} (g : A ⟶ B) : Prop :=
  Function.Surjective (fun x : B ⟶ Y (n - 1) => g ≫ x) ∧ Function.Injective (fun x : B ⟶ Y n => g ≫ x)

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] in
theorem inj_iff {A B X : D} (g : A ⟶ B) :
    Function.Injective (fun x : B ⟶ X => g ≫ x) ↔ ∀ x : B ⟶ X, g ≫ x = 0 → x = 0 := by
  constructor
  · intro h x hx; exact h (by simpa using hx)
  · intro h x y hxy
    have := h (x - y) (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.2 hxy)
    exact sub_eq_zero.1 this

theorem relY_mid (T₁ T₂ : Triangle D) (h₁ : T₁ ∈ distTriang D) (h₂ : T₂ ∈ distTriang D) (φ : T₁ ⟶ T₂)
    (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧) (n : ℤ)
    (ha : RelY Y n φ.hom₁) (hc : RelY Y n φ.hom₃) : RelY Y n φ.hom₂ := by
  have hci := (inj_iff _).1 hc.2
  have hai := (inj_iff _).1 ha.2
  refine ⟨fun x => ?_, (inj_iff _).2 fun d hd => ?_⟩
  · obtain ⟨y, hy⟩ := ha.1 (T₁.mor₁ ≫ x)
    simp only at hy
    have ho : T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y ≫ (e n).inv = 0 := by
      apply hci
      rw [← Category.assoc, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc, hy, Functor.map_comp_assoc,
        ← Category.assoc, comp_distTriang_mor_zero₃₁ T₁ h₁, zero_comp]
    have ho' : T₂.rotate.mor₂ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y = 0 := by
      have := congrArg (· ≫ (e n).hom) ho
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] at this
      exact this
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ h₂) _ ho'
    obtain ⟨(z : T₂.obj₂ ⟶ Y (n - 1)), rfl⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective g
    have hyz : y = T₂.mor₁ ≫ (-z) := by
      apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
      rw [hg]
      simp only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]
      exact Preadditive.neg_comp _ _
    have hw : T₁.mor₁ ≫ (x - φ.hom₂ ≫ (-z)) = 0 := by
      rw [Preadditive.comp_sub, ← hy, hyz, ← Category.assoc, ← φ.comm₁, Category.assoc, sub_self]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ h₁ _ hw
    obtain ⟨w', hw'⟩ := hc.1 w
    simp only at hw'
    refine ⟨-z + T₂.mor₂ ≫ w', ?_⟩
    simp only
    rw [Preadditive.comp_add, ← Category.assoc, ← φ.comm₂, Category.assoc, hw', ← hw]
    abel
  · have h1 : T₂.mor₁ ≫ d = 0 := by
      apply hai
      rw [← Category.assoc, ← φ.comm₁, Category.assoc, hd, comp_zero]
    obtain ⟨h, rfl⟩ := Triangle.yoneda_exact₂ _ h₂ _ h1
    have h3 : T₁.mor₂ ≫ φ.hom₃ ≫ h = 0 := by
      rw [← Category.assoc, φ.comm₂, Category.assoc, hd]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ h₁ _ h3
    obtain ⟨k', hk'⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (k ≫ (e n).hom)
    obtain ⟨k'', hk''⟩ := ha.1 k'
    simp only at hk''
    have hm : h = T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map k'' ≫ (e n).inv := by
      rw [← sub_eq_zero]
      apply hci
      rw [Preadditive.comp_sub, hk, ← Category.assoc φ.hom₃, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc,
        hk'', hk', Category.assoc, Iso.hom_inv_id, Category.comp_id, sub_self]
    rw [hm, ← Category.assoc, comp_distTriang_mor_zero₂₃ _ h₂, zero_comp]

end Tri

section Bridge
open CochainComplex CochainComplex.HomComplex
variable (R : Type) [CommRing R]

abbrev Yres (F : Shv R) (m : ℤ) : HomotopyCategory (Shv R) (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦m⟧)

theorem pull_eq_comp {K L : Cx R} (f : K ⟶ L) (F : Shv R) (m : ℤ) :
    (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶ Yres R F m =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R f F m) ∘ (CohomologyClass.homAddEquiv.symm) := by
  funext g
  simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  congr 1
  exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm

theorem relK_iff {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) :
    RelK R F n f ↔ Tri.RelY (Yres R F) n ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f) := by
  unfold Tri.RelY RelK
  rw [pull_eq_comp, pull_eq_comp, EquivLike.comp_surjective, EquivLike.surjective_comp,
    EquivLike.comp_injective, EquivLike.injective_comp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 (n - 1) (by omega), h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨fun m hm => ?_, h2⟩; obtain rfl : m = n - 1 := (by omega)
    exact h1

def yresIso (F : Shv R) (m : ℤ) : Yres R F m ≅ (Yres R F (m - 1))⟦(1 : ℤ)⟧ :=
  LateralTheory.E.E8.ExciseCut.ConeZeroPf.shIso R (res R F) m

end Bridge

def pieceC (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (K.X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (L.X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (f.f (-(p : ℤ)))

def Tower : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def TowerFin : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ) (P : ℕ),
  (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def Trunc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧
    ((∀ p : ℕ, RelK R F n (pieceC R f p)) → ∀ p : ℕ, RelK R F n (pieceC R f' p)) ∧
    (RelK R F n f' → RelK R F n f)

theorem tower_of (hB : TowerFin) (hT : Trunc) : Tower := by
  intro R _ F K L f n hz hp
  obtain ⟨P, K', L', f', hz', hpp, hback⟩ := hT R F f n hz
  exact hback (hB R F f' n P hz' (hpp hp))

theorem chains_X_isZero (R : Type) [CommRing R] (U : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj U).X i) := by
  change IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  have e : ComplexShape.embeddingDownNat.f j = -(j : ℤ) := rfl
  omega

end LateralTheory.E.FiltPf

open LateralTheory.E.FiltPf in
theorem LateralTheory.E.TruncationPieces.Filt_of_tower (hT : Tower) : LateralTheory.E.TruncationPieces.Filt := by
  intro R _ F U E u n h
  exact hT R F ((chains R).map u) n (fun i hi => ⟨chains_X_isZero R U i hi, chains_X_isZero R E i hi⟩) h

open LateralTheory.E.FiltPf in
theorem LateralTheory.E.TruncationPieces.Filt_of (hB : TowerFin) (hT : Trunc) : LateralTheory.E.TruncationPieces.Filt :=
  LateralTheory.E.TruncationPieces.Filt_of_tower (tower_of hB hT)
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

namespace LateralTheory.E.GluePf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] : Subsingleton (Sec F X) := by
  have hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X := Scheme.bot_mem_grothendieckTopology X
  have h1 : (𝟙 (F.obj.obj (op X))) = 0 := by
    apply ((F.cond (F.obj.obj (op X))) _ hb).isSeparatedFor.ext
    intro Y f hf
    exact hf.elim
  constructor
  intro a b
  have ha : a = 0 := by
    have := congrArg (fun φ => (φ : F.obj.obj (op X) ⟶ _).hom a) h1
    simpa using this
  have hb' : b = 0 := by
    have := congrArg (fun φ => (φ : F.obj.obj (op X) ⟶ _).hom b) h1
    simpa using this
  rw [ha, hb']

theorem pull_inj_of_initial {R : Type} [CommRing R] {F : Shv R} {X Y : Scheme.{0}} (hX : IsInitial X) (f : Y ⟶ X) (n : ℤ)
    (x : H R (sch.obj X) F n) (hx : pull R (sch.map f) F n x = 0) : x = 0 := by
  have e : hX.to Y ≫ f = 𝟙 X := hX.hom_ext _ _
  have : x = pull R (sch.map (hX.to Y ≫ f)) F n x := by rw [e, CategoryTheory.Functor.map_id, pull_id]
  rw [this, Functor.map_comp, pull_comp, hx, map_zero]

theorem ht_sub (H : Hyp) (q : ℕ) (i n : ℤ) (X : Scheme.{0}) [IsEmpty X] : Subsingleton (Ht q (sch.obj X) n i) := by
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact (H.a9 (ZMod q) (tw q i)).1 _ n h
  · obtain ⟨e, -⟩ := (H.a9 (ZMod q) (tw q i)).2
    have := sec_sub (tw q i) X
    exact ⟨fun a b => (e X).symm.injective (Subsingleton.elim _ _)⟩
  · constructor
    have key : ∀ x : Ht q (sch.obj X) n i, x = 0 := by
      intro x
      obtain ⟨Y, f, -, -, hf⟩ := H.a5 (ZMod q) X (tw q i) n h x
      exact pull_inj_of_initial (isInitialOfIsEmpty) f n x hf
    intro a b; rw [key a, key b]

def cmp {X : Scheme.{0}} (O : X.Opens) (hO : IsClosed (O : Set X)) : X.Opens := ⟨(O : Set X)ᶜ, hO.isOpen_compl⟩

theorem mem_ι {X : Scheme.{0}} (U : X.Opens) (p : U) : U.ι p ∈ U := by
  have : U.ι p ∈ Set.range U.ι := ⟨p, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

theorem vanish_of_range {R : Type} [CommRing R] {F : Shv R} {X U Z : Scheme.{0}} (u : U ⟶ X) [IsOpenImmersion u] (g : Z ⟶ X)
    (hg : Set.range g ⊆ Set.range u) (n : ℤ) (v : H R (sch.obj X) F n) (hv : pull R (sch.map u) F n v = 0) :
    pull R (sch.map g) F n v = 0 := by
  rw [← IsOpenImmersion.lift_fac u g hg, CategoryTheory.Functor.map_comp, pull_comp, hv, map_zero]

theorem empty_pb' {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2) :
    IsEmpty ((pullback O1.ι O2.ι : Scheme.{0})) := by
  constructor; intro p
  have h := congrArg (fun φ => φ p) (pullback.condition (f := O1.ι) (g := O2.ι))
  simp only [Scheme.Hom.comp_apply] at h
  have a := mem_ι O1 (pullback.fst O1.ι O2.ι p)
  have b := mem_ι O2 (pullback.snd O1.ι O2.ι p)
  rw [← h] at b
  exact hd _ a b

theorem cover' {X : Scheme.{0}} (O1 O2 : X.Opens) (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) :
    Set.range O1.ι ∪ Set.range O2.ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  ext p; simp only [Set.mem_union, Set.mem_univ, iff_true]; exact hc p

theorem two_inj' (hM : MV) (H : Hyp) (q : ℕ) (i : ℤ) {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2)
    (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) (n : ℤ)
    (x : Ht q (sch.obj X) n i) (h1 : pull _ (sch.map O1.ι) _ _ x = 0) (h2 : pull _ (sch.map O2.ι) _ _ x = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨δ, hex, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨w, rfl⟩ := ((hex O1.ι O2.ι (cover' O1 O2 hc) m).2.2 x).1 ⟨h1, h2⟩
  have := empty_pb' O1 O2 hd
  have := ht_sub H q i m (pullback O1.ι O2.ι)
  rw [Subsingleton.elim w 0, map_zero]

theorem inj_fin (hM : MV) (H : Hyp) (q : ℕ) (i n : ℤ) : ∀ (k : ℕ) {X : Scheme.{0}} (O : Fin k → X.Opens),
    (∀ j, IsClosed (O j : Set X)) → (∀ p : X, ∃ j, p ∈ O j) → ∀ x : Ht q (sch.obj X) n i,
    (∀ j, pull _ (sch.map (O j).ι) _ _ x = 0) → x = 0 := by
  intro k
  induction k with
  | zero =>
    intro X O _ hc x _
    have : IsEmpty X := ⟨fun p => (hc p).elim fun j _ => j.elim0⟩
    have := ht_sub H q i n X
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro X O hO hc x hx
    let A := O (Fin.last k)
    let C := cmp A (hO _)
    refine two_inj' hM H q i A C (fun p h1 h2 => h2 h1) (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n x
      (hx _) ?_
    refine ih (fun j => C.ι ⁻¹ᵁ O j.castSucc) (fun j => (hO _).preimage C.ι.continuous) ?_ _ ?_
    · intro p
      obtain ⟨j, hj⟩ := hc (C.ι p)
      have hpc := mem_ι C p
      cases j using Fin.lastCases with
      | last => exact absurd hj hpc
      | cast j' => exact ⟨j', hj⟩
    · intro j
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp]
      refine vanish_of_range (O j.castSucc).ι _ ?_ n x (hx _)
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact mem_ι _ p

theorem two_glue' (hM : MV) (H : Hyp) (q : ℕ) (i : ℤ) {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2)
    (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) (n : ℤ) (a : Ht q (sch.obj O1) n i) (b : Ht q (sch.obj O2) n i) :
    ∃ x : Ht q (sch.obj X) n i, pull _ (sch.map O1.ι) _ _ x = a ∧ pull _ (sch.map O2.ι) _ _ x = b := by
  obtain ⟨δ, hex, -⟩ := hM H (ZMod q) (tw q i)
  have := empty_pb' O1 O2 hd
  have := ht_sub H q i n (pullback O1.ι O2.ι)
  exact (hex O1.ι O2.ι (cover' O1 O2 hc) n).1 a b (Subsingleton.elim _ _)

theorem surj_fin (hM : MV) (H : Hyp) (q : ℕ) (i n : ℤ) {X P : Scheme.{0}} (φ : P ⟶ X) (z : Ht q (sch.obj P) n i) :
    ∀ (k : ℕ) (O : Fin k → X.Opens), (∀ j, IsClosed (O j : Set X)) →
    (∀ j, ∃ w : Ht q (sch.obj (O j)) n i, pull _ (sch.map (φ ∣_ O j)) _ _ w = pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ z) →
    ∃ x : Ht q (sch.obj X) n i, ∀ j, pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ (pull _ (sch.map φ) _ _ x) =
      pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ z := by
  intro k
  induction k with
  | zero => intro O _ _; exact ⟨0, fun j => j.elim0⟩
  | succ k ih =>
    intro O hO hW
    obtain ⟨x, hx⟩ := ih (fun j => O j.castSucc) (fun j => hO _) (fun j => hW _)
    let A := O (Fin.last k)
    let C := cmp A (hO _)
    obtain ⟨w, hw⟩ := hW (Fin.last k)
    obtain ⟨x', h1, h2⟩ := two_glue' hM H q i A C (fun p h1 h2 => h2 h1)
      (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n w (pull _ (sch.map C.ι) _ _ x)
    have agreeA : pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ (pull _ (sch.map φ) _ _ x') = pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ z := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, ← morphismRestrict_ι, CategoryTheory.Functor.map_comp, pull_comp, h1]
      exact hw
    refine ⟨x', fun j => ?_⟩
    cases j using Fin.lastCases with
    | last => exact agreeA
    | cast j' =>
      rw [← sub_eq_zero, ← map_sub]
      let V := φ ⁻¹ᵁ O j'.castSucc
      refine two_inj' hM H q i (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A)) (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ C)) (fun p h1 h2 => h2 h1)
        (fun p => by by_cases h : p ∈ V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A); exacts [Or.inl h, Or.inr h]) n _ ?_ ?_
      · rw [← pull_comp, ← CategoryTheory.Functor.map_comp]
        refine vanish_of_range (φ ⁻¹ᵁ A).ι _ ?_ n _ (by rw [map_sub, agreeA, sub_self])
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        simp only [Scheme.Hom.comp_apply]
        exact mem_ι _ p
      · have e : pull _ (sch.map φ) _ _ x' - z = pull _ (sch.map φ) _ _ (x' - x) + (pull _ (sch.map φ) _ _ x - z) := by
          rw [map_sub]; abel
        rw [e, map_add, map_add, map_sub (pull _ (sch.map V.ι) _ _), hx j', sub_self, map_zero, add_zero,
          ← pull_comp, ← pull_comp, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        refine vanish_of_range C.ι _ ?_ n _ (by rw [map_sub, h2, sub_self])
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        simp only [Scheme.Hom.comp_apply]
        exact mem_ι _ p

theorem hit_opens (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}}
    (g : Y ⟶ Spec (CommRingCat.of A)) (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) [IsOpenImmersion u]
    (O : Y.Opens) (hO : (O : Set Y) = Set.range u) (h : Hit q i n g z u) :
    ∃ w : Ht q (sch.obj O) n i, pull _ (sch.map (pullback.fst g (cpt A) ∣_ O)) _ _ w =
      pull _ (sch.map (pullback.fst g (cpt A) ⁻¹ᵁ O).ι) _ _ z := by
  obtain ⟨w, hw⟩ := h
  have hr : Set.range O.ι ⊆ Set.range u := by rw [Scheme.Opens.range_ι, hO]
  let r := IsOpenImmersion.lift u O.ι hr
  have hr' : r ≫ u = O.ι := IsOpenImmersion.lift_fac _ _ _
  have hr'' : ∀ {Z : Scheme.{0}} (t : Y ⟶ Z), r ≫ u ≫ t = O.ι ≫ t := by
    intro Z t; rw [← Category.assoc, hr']
  let e : ((pullback.fst g (cpt A) ⁻¹ᵁ O : Scheme.{0})) ⟶ pullback (u ≫ g) (cpt A) :=
    pullback.lift ((pullback.fst g (cpt A) ∣_ O) ≫ r) ((pullback.fst g (cpt A) ⁻¹ᵁ O).ι ≫ pullback.snd g (cpt A))
      (by rw [Category.assoc, hr'', morphismRestrict_ι_assoc, pullback.condition, Category.assoc])
  have he : e ≫ fm u g = (pullback.fst g (cpt A) ⁻¹ᵁ O).ι := by
    unfold fm
    apply pullback.hom_ext
    · simp only [e, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hr', morphismRestrict_ι, pullback.map]
    · simp only [e, Category.assoc, pullback.lift_snd, Category.comp_id, pullback.map]
  refine ⟨pull _ (sch.map r) _ _ w, ?_⟩
  have h2 : (pullback.fst g (cpt A) ∣_ O) ≫ r = e ≫ pullback.fst (u ≫ g) (cpt A) := (pullback.lift_fst _ _ _).symm
  rw [← pull_comp, ← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp, pull_comp, hw, ← pull_comp,
    ← CategoryTheory.Functor.map_comp, he]

theorem fin_cover {Y : Scheme.{0}} [CompactSpace Y] (O : Y → Y.Opens) (hO : ∀ y, y ∈ O y) :
    ∃ (k : ℕ) (f : Fin k → Y), ∀ p, ∃ j, p ∈ O (f j) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (O y : Set Y)) (fun y => (O y).isOpen)
    (fun p _ => Set.mem_iUnion.2 ⟨p, hO p⟩)
  refine ⟨t.card, fun j => (t.equivFin.symm j).1, fun p => ?_⟩
  obtain ⟨y, hy, hp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hp⟩

def rg {U Y : Scheme.{0}} (u : U ⟶ Y) (h : IsOpenImmersion u) : Y.Opens := ⟨Set.range u, u.isOpenEmbedding.isOpen_range⟩

theorem rg_closed {U Y : Scheme.{0}} (u : U ⟶ Y) (h : IsOpenImmersion u) (h' : IsClosedImmersion u) :
    IsClosed (rg u h : Set Y) := u.isClosedEmbedding.isClosed_range

theorem glue_of : Glue := by
  intro hM H q i A _ _ hq Y _ _ g n hI hS
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    choose U u hu using hI x hx
    obtain ⟨k, f, hf⟩ := fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)
    refine inj_fin hM H q i n k (fun j => rg (u (f j)) (hu (f j)).1) (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1) hf x ?_
    intro j
    have := (hu (f j)).1
    exact vanish_of_range (u (f j)) _ (by rw [Scheme.Opens.range_ι]; exact fun _ h => h) n x (hu (f j)).2.2.2
  · intro z
    choose U u hu using hS z
    obtain ⟨k, f, hf⟩ := fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)
    obtain ⟨x, hx⟩ := surj_fin hM H q i n (pullback.fst g (cpt A)) z k (fun j => rg (u (f j)) (hu (f j)).1)
      (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1)
      (fun j => by have := (hu (f j)).1; exact hit_opens q i n g z (u (f j)) _ rfl (hu (f j)).2.2.2)
    refine ⟨x, ?_⟩
    rw [← sub_eq_zero]
    refine inj_fin hM H q i n k (fun j => pullback.fst g (cpt A) ⁻¹ᵁ rg (u (f j)) (hu (f j)).1)
      (fun j => (rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1).preimage (pullback.fst g (cpt A)).continuous) (fun p => hf _) _ ?_
    intro j
    rw [map_sub, hx j, sub_self]

end LateralTheory.E.GluePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LSchClsPfYon
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sch_clsPfYon

variable (R : Type) [CommRing R]

def yon0 (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (freeP R).obj (yoneda.obj X) ⟶ G.val where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (U.unop ⟶ X)) (TypeCat.ofHom (fun g : ULift.{1} (U.unop ⟶ X) => (G.val.map g.down.op).hom z))
  naturality U V f := by
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    have e1 : (((freeP R).obj (yoneda.obj X)).map f).hom (ModuleCat.freeMk (ULift.up g)) =
        ModuleCat.freeMk (ULift.up (f.unop ≫ g)) := ModuleCat.free_map_apply (R := ULift.{1} R) _ _
    erw [ConcreteCategory.comp_apply, e1, ConcreteCategory.comp_apply, ModuleCat.freeDesc_apply]
    erw [ModuleCat.freeDesc_apply]
    show (G.val.map (f.unop ≫ g).op).hom z = (G.val.map f).hom ((G.val.map g.op).hom z)
    rw [op_comp, Functor.map_comp]
    rfl

def yon (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (free R).obj (yoneda.obj X) ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.cond⟩

theorem yon_gen (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : Sec.map (yon R G X z) (freeGen R _ X (𝟙 X)) = z := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.cond
  have := congrArg (fun φ => (φ.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) h
  refine this.trans ?_
  dsimp only [yon0]
  erw [ModuleCat.freeDesc_apply]
  simp

theorem yon_ext {G : Shv R} {X : Scheme.{0}} (φ ψ : (free R).obj (yoneda.obj X) ⟶ G)
    (h : Sec.map φ (freeGen R _ X (𝟙 X)) = Sec.map ψ (freeGen R _ X (𝟙 X))) : φ = ψ := by
  have key : ∀ (U : Scheme.{0}) (g : U ⟶ X), Sec.map φ (freeGen R _ U g) = Sec.map ψ (freeGen R _ U g) := by
    intro U g
    have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
      rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
      simp
    rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, h]
  have hv : φ.hom = ψ.hom := by
    apply sheafify_hom_ext Scheme.etaleTopology _ _ G.cond
    refine NatTrans.ext (funext fun U => ?_)
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    exact key U.unop g
  first | exact Sheaf.hom_ext hv | (cases φ; cases ψ; cases hv; rfl)

theorem yon_res {G : Shv R} {X : Scheme.{0}} (z : Sec G X) (U : Scheme.{0}) (g : U ⟶ X) :
    Sec.map (yon R G X z) (freeGen R _ U g) = Sec.res g z := by
  have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
    rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
    simp
  rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, yon_gen]

end LateralTheory.E.L_sch_clsPfYon
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LZIdemSumApprox
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.IdempotentLiftingAlt

def LZIdemSumNoeth : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

def LZIdemSumApprox : Prop := LZIdemSumNoeth → ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_le (S : Subalgebra A K) : mS S ≤ Subalgebra.toSubmodule S := by
  unfold mS
  exact Submodule.smul_le_right

theorem lift_of_sum (B C : Subalgebra A K) (e f : K) (he : e ∈ B) (hf : f ∈ C) (h : e - f ∈ mS B ⊔ mS C) :
    ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C := by
  obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp h
  have hβB : β ∈ B := mS_le B hβ
  have hγC : γ ∈ C := mS_le C hγ
  refine ⟨e - β, B.sub_mem he hβB, ?_, ?_, ?_⟩
  · have : e - β = f + γ := by linear_combination -hsum
    rw [this]; exact C.add_mem hf hγC
  · have : e - β - e = -β := by ring
    rw [this]; exact (mS B).neg_mem hβ
  · have : e - β - f = γ := by linear_combination -hsum
    rw [this]; exact hγ

theorem IdemLift_of (hN : LZIdemSumNoeth) (hA : LZIdemSumApprox) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.IdemLift := by
  intro A _ _ _ K _ _ B C t hc e f hp
  exact lift_of_sum B C e f hp.1 hp.2.1 (hA hN A K B C t hc e f hp)

end LateralTheory.E.IdempotentLiftingAlt
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafMVVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafMVVanishPf

theorem mvSpc : LateralTheory.E.MVPf.MVSpc :=
  LateralTheory.E.MVPf.MVSpc_of (fun R _ _ _ _ f g h => LateralTheory.Fin.EtaleMayerVietorisChainsShortExact.intersectionNumber_baseChange R f g h)

end LateralTheory.E.LeafMVVanishPf

namespace LateralTheory.E.E8
open LateralTheory.E.LeafMVVanishPf

end LateralTheory.E.E8
end
end

