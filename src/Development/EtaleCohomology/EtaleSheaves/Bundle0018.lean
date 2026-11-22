import Development.EtaleCohomology.EtaleSheaves.Bundle0006

-- bundled from Development.EtaleCohomology.EtaleSheaves.CompPf
section
noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.CompPf
open LateralTheory.E.t_E3Cut

section
variable {R D : Type} [CommRing R] [CommRing D] (h : R →+* D)

theorem eval_map_rr (p : R[X]) (x : D) :
    (p.map h.rangeRestrict).eval₂ h.range.subtype x = p.eval₂ h x := by
  rw [eval₂_map]; rfl

theorem alg_of (x : D) (p : R[X]) (n : ℕ) (hn : h (p.coeff n) ≠ 0) (hp : p.eval₂ h x = 0) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra
    IsAlgebraic h.range x := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  refine ⟨p.map h.rangeRestrict, ?_, ?_⟩
  · intro h0
    apply hn
    have h1 := congrArg (fun q => ((q.coeff n : h.range) : D)) h0
    simpa using h1
  · rw [aeval_def]; exact (eval_map_rr h p x).trans hp

theorem of_alg (x : D) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra
    IsAlgebraic h.range x → ∃ p : R[X], (∃ n, h (p.coeff n) ≠ 0) ∧ p.eval₂ h x = 0 := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  rintro ⟨q, hq0, hq⟩
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective h.rangeRestrict h.rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simpa using hc n
  · rw [aeval_def] at hq; exact (eval_map_rr h p x).symm.trans hq
end

theorem Comp_of : LateralTheory.E.AlgResPropsPf.Comp := by
  intro A B C f g hf hg Q hQ c
  haveI := hQ
  let gB : B →+* C ⧸ Q := (Ideal.Quotient.mk Q).comp g.hom
  let fA : A →+* C ⧸ Q := gB.comp f.hom
  have hle : fA.range ≤ gB.range := by rintro _ ⟨a, rfl⟩; exact ⟨f.hom a, rfl⟩
  letI : Algebra fA.range (C ⧸ Q) := fA.range.subtype.toAlgebra
  letI : Algebra gB.range (C ⧸ Q) := gB.range.subtype.toAlgebra
  letI : Algebra fA.range gB.range := (Subring.inclusion hle).toAlgebra
  haveI : IsScalarTower fA.range gB.range (C ⧸ Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI h1 : Algebra.IsAlgebraic fA.range gB.range := ⟨by
    rintro ⟨_, b, rfl⟩
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap g.hom) (hQ.comap _) b
    have hb := alg_of fA (gB b) p n (by
        intro h0; apply hn; rw [Ideal.mem_comap]; exact Ideal.Quotient.eq_zero_iff_mem.mp h0)
      (by
        have h5 : (Ideal.Quotient.mk Q) (g.hom (p.eval₂ f.hom b)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂, hom_eval₂] at h5; exact h5)
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom fA.range gB.range (C ⧸ Q)) Subtype.val_injective).mp hb⟩
  haveI h2 : Algebra.IsAlgebraic gB.range (C ⧸ Q) := ⟨by
    intro x
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hg Q hQ c'
    exact alg_of gB _ p n (fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      (by
        have h5 : (Ideal.Quotient.mk Q) (p.eval₂ g.hom c') = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂] at h5; exact h5)⟩
  have h3 := (Algebra.IsAlgebraic.trans fA.range gB.range (C ⧸ Q)).1 (Ideal.Quotient.mk Q c)
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := of_alg fA _ h3
  refine ⟨p, ⟨n, fun hm => hn (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hom_eval₂]; exact hp

end LateralTheory.E.CompPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContAffPf

lemma isoSpec_inv_nat {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map f.appTop ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]

lemma pp {R : Type} [CommRing R] {A B C E : Spc} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ C) (d : C ⟶ E) (h : a ≫ b = c ≫ d)
    (F : Shv R) (n : ℤ) (x : H R E F n) : pull R a F n (pull R b F n x) = pull R c F n (pull R d F n x) := by
  rw [← pull_comp, h, pull_comp]

theorem aff_case (hB1 : B1) (q : ℕ) {I : Type} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    (hc : IsLimit c) (ha : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)) (hcs : ∀ j, CompactSpace (D.obj j))
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j)) (hu : ∀ j, IsUnit (q : Γ(D.obj j, ⊤)))
    (hA : ∀ j, IsAffine (D.obj j)) (hP : IsAffine c.pt) (n i : ℤ) :
    (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
    ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
      ∃ (k : I) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0 := by
  obtain ⟨hE⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  have hP' : ∀ j, IsAffine (((Functor.const I).obj c.pt).obj j) := fun _ => hP
  have B := hB1 q (D.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hE n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := I)
  have huP : IsUnit (q : Γ(c.pt, ⊤)) := by
    have := (hu j0).map (c.π.app j0).appTop.hom
    simpa using this
  constructor
  · intro x
    obtain ⟨j, y, hy⟩ := B.1 (pull _ (sch.map c.pt.isoSpec.inv) _ _ x) huP
    refine ⟨j.unop, pull _ (sch.map (D.obj j.unop).isoSpec.hom) _ _ y, ?_⟩
    have key := pp (R := ZMod q) (sch.map (c.π.app j.unop)) (sch.map (D.obj j.unop).isoSpec.hom)
      (sch.map c.pt.isoSpec.hom) (sch.map (Spec.map (c.π.app j.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n y
    refine key.trans ?_
    have hy' : pull (ZMod q) (sch.map (Spec.map (c.π.app j.unop).appTop)) (tw q i) n y =
      pull (ZMod q) (sch.map c.pt.isoSpec.inv) (tw q i) n x := hy
    rw [hy', ← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, pull_id]
  · intro j y hy
    obtain ⟨k, f, hk⟩ := B.2 (Opposite.op j) (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) (hu j) (by
      have key2 := pp (R := ZMod q) (sch.map (Spec.map (c.π.app j).appTop)) (sch.map (D.obj j).isoSpec.inv)
        (sch.map c.pt.isoSpec.inv) (sch.map (c.π.app j))
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (isoSpec_inv_nat _)) (tw q i) n y
      exact key2.trans (by rw [hy]; exact map_zero _))
    refine ⟨k.unop, f.unop, ?_⟩
    have e1 : y = pull _ (sch.map (D.obj j).isoSpec.hom) _ _ (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
    rw [e1]
    have key3 := pp (R := ZMod q) (sch.map (D.map f.unop)) (sch.map (D.obj j).isoSpec.hom)
      (sch.map (D.obj k.unop).isoSpec.hom) (sch.map (Spec.map (D.map f.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y)
    refine key3.trans ?_
    have hk' : pull (ZMod q) (sch.map (Spec.map (D.map f.unop).appTop)) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) = 0 := hk
    rw [hk', map_zero]

theorem ContAff_of : ContAff := by
  intro h X _ q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : IsAffine (D.obj j0) := IsAffine.of_isIso e.hom
  have hc' : IsLimit (c.whisker (Over.forget j0)) := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j0) c).symm hc
  have hA : ∀ k : Over j0, IsAffine ((Over.forget j0 ⋙ D).obj k) := fun k => by
    have i1 := ha k.hom
    have i2 : IsAffine (D.obj ((Functor.fromPUnit j0).obj k.right)) := ‹IsAffine (D.obj j0)›
    exact @isAffine_of_isAffineHom _ _ (D.map k.hom) (ha k.hom) i2
  have hP : IsAffine c.pt := by
    have : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f) := ha
    have := hcs; have := hqs
    have := isAffineHom_π_app D c hc j0
    exact isAffine_of_isAffineHom (c.π.app j0)
  have R := aff_case h.b1 q (Over.forget j0 ⋙ D) (c.whisker (Over.forget j0)) hc' (fun f => ha _)
    (fun k => hcs _) (fun k => hqs _) (fun k => hu _) hA hP n i
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨k, y, hy⟩ := R.1 x
    exact ⟨k.left, y, hy⟩
  · obtain ⟨k, g, h0, -⟩ := IsCofilteredOrEmpty.cone_objs j j0
    obtain ⟨l, f, hf⟩ := R.2 (Over.mk h0) (pull _ (sch.map (D.map g)) _ _ y) (by
      show pull _ (sch.map (c.π.app k)) _ _ _ = 0
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, c.w]
      exact hy)
    refine ⟨l.left, f.left ≫ g, ?_⟩
    rw [D.map_comp, CategoryTheory.Functor.map_comp, pull_comp]
    exact hf

end LateralTheory.E.ContAffPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContIndPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ContIndPf

section lists
variable {X : Scheme.{0}}

def lsup (l : List X.Opens) : X.Opens := l.foldr (· ⊔ ·) ⊥

lemma lsup_cons (a : X.Opens) (l : List X.Opens) : lsup (a :: l) = a ⊔ lsup l := rfl
lemma lsup_nil : lsup ([] : List X.Opens) = ⊥ := rfl

lemma le_lsup {l : List X.Opens} {B : X.Opens} (h : B ∈ l) : B ≤ lsup l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [lsup_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_sup_left
    · exact (ih h).trans le_sup_right

lemma lsup_le {l : List X.Opens} {W : X.Opens} (h : ∀ B ∈ l, B ≤ W) : lsup l ≤ W := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons]
    exact sup_le (h a (by simp)) (ih fun B hB => h B (by simp [hB]))

lemma isCompact_lsup (l : List X.Opens) (h : ∀ B ∈ l, IsCompact (B : Set X)) : IsCompact (lsup l : Set X) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, TopologicalSpace.Opens.coe_sup]
    exact (h a (by simp)).union (ih fun B hB => h B (by simp [hB]))

lemma preimage_lsup {Y : Scheme.{0}} (f : Y ⟶ X) (l : List X.Opens) :
    f ⁻¹ᵁ lsup l = lsup (l.map (f ⁻¹ᵁ ·)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, List.map_cons, lsup_cons, ← ih]
    rfl

lemma lsup_inf (l : List X.Opens) (A : X.Opens) : lsup l ⊓ A = lsup (l.map (· ⊓ A)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih => rw [List.map_cons, lsup_cons, lsup_cons, inf_sup_right, ih]

end lists

section opens
variable {X : Scheme.{0}}

lemma image_le_range {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A : Y.Opens) : f ''ᵁ A ≤ f.opensRange := by
  rw [← Scheme.Hom.image_top_eq_opensRange]
  exact (f.image_le_image_iff _ _).2 le_top

lemma image_inf {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A B : Y.Opens) :
    f ''ᵁ (A ⊓ B) = f ''ᵁ A ⊓ f ''ᵁ B := by
  apply le_antisymm
  · exact le_inf ((f.image_le_image_iff _ _).2 inf_le_left) ((f.image_le_image_iff _ _).2 inf_le_right)
  · have hC : f ''ᵁ A ⊓ f ''ᵁ B = f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B)) := by
      rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 (inf_le_left.trans (image_le_range f A))]
    rw [hC, f.image_le_image_iff]
    have : f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B) = f ⁻¹ᵁ (f ''ᵁ A) ⊓ f ⁻¹ᵁ (f ''ᵁ B) := rfl
    rw [this, f.preimage_image_eq, f.preimage_image_eq]

lemma image_le (W : X.Opens) (A : W.toScheme.Opens) : W.ι ''ᵁ A ≤ W :=
  (image_le_range W.ι A).trans (Scheme.Opens.opensRange_ι W).le

lemma affine_preimage (W : X.Opens) {B : X.Opens} (h : B ≤ W) (hB : IsAffineOpen B) :
    IsAffineOpen (W.ι ⁻¹ᵁ B) := by
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rwa [W.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h]

def Good (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsAffineOpen (A ⊓ B)

def Good2 (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsCompact ((A ⊓ B : Y.Opens) : Set Y)

lemma good_of (W : X.Opens)
    (h : ∀ C D : X.Opens, C ≤ W → D ≤ W → IsAffineOpen C → IsAffineOpen D → IsAffineOpen (C ⊓ D)) :
    Good W.toScheme := by
  intro A B hA hB
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rw [image_inf]
  exact h _ _ (image_le W A) (image_le W B) (hA.image_of_isOpenImmersion _) (hB.image_of_isOpenImmersion _)

lemma good_open (hX : Good X) (W : X.Opens) : Good W.toScheme :=
  good_of W (fun C D _ _ hC hD => hX C D hC hD)

lemma good_affine (A W : X.Opens) (hA : IsAffineOpen A) (hW : W ≤ A) : Good W.toScheme := by
  apply good_of W
  intro C D hC hD hC' hD'
  have : IsAffine A.toScheme := hA
  have h1 := (affine_preimage A (hC.trans hW) hC').inf (affine_preimage A (hD.trans hW) hD')
  have h2 := h1.image_of_isOpenImmersion A.ι
  rwa [image_inf, A.ι.image_preimage_eq_opensRange_inf, A.ι.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.2 (hC.trans hW), inf_eq_right.2 (hD.trans hW)] at h2

lemma hasCompactAffineIntersections_open_subscheme (hX : Good2 X) (W : X.Opens) : Good2 W.toScheme := by
  intro A B hA hB
  have h := hX _ _ (hA.image_of_isOpenImmersion W.ι) (hB.image_of_isOpenImmersion W.ι)
  rw [← image_inf] at h
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  convert h using 1
  simp

lemma exists_cover (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ l : List X.Opens, (∀ B ∈ l, IsAffineOpen B ∧ B ≤ W) ∧ lsup l = W := by
  let ι := {B : X.Opens // IsAffineOpen B ∧ B ≤ W}
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun i : ι => ((i.1 : X.Opens) : Set X)) (fun i => i.1.isOpen)
    (by
      intro x hx
      have hb : ∀ {U : X.Opens} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
      obtain ⟨B, hB, hxB, hBW⟩ := hb (U := W) hx
      exact Set.mem_iUnion.2 ⟨⟨B, hB, hBW⟩, hxB⟩)
  refine ⟨t.toList.map Subtype.val, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
    exact i.2
  · apply le_antisymm
    · apply lsup_le
      intro B hB
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
      exact i.2.2
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact le_lsup (List.mem_map.2 ⟨i, Finset.mem_toList.2 hi, rfl⟩) hxi

end opens

section ind
variable (P : Scheme.{0} → Prop) (hA : ∀ (X : Scheme.{0}) [IsAffine X], P X)
  (hS : ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X)
include hA hS

omit hS in
lemma empty_case (Y : Scheme.{0}) (htop : lsup ([] : List Y.Opens) = ⊤) : P Y := by
  have : IsEmpty Y := by
    constructor
    intro x
    have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [← htop, lsup_nil] at hx
    exact hx
  exact hA Y

lemma stage1 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · apply ih (lsup l ⊓ A).toScheme ((l.map (· ⊓ A)).map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp [hl])
          (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
          refine affine_preimage _ ?_ (hG D A (hlA D hD) hAff)
          rw [lsup_inf]
          exact le_lsup (List.mem_map.2 ⟨D, hD, rfl⟩)
        · rw [← preimage_lsup, ← lsup_inf, Scheme.Opens.ι_preimage_self]

lemma stage2 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good2 Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (hasCompactAffineIntersections_open_subscheme hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · have hc : IsCompact ((lsup l ⊓ A : Y.Opens) : Set Y) := by
          rw [lsup_inf]
          apply isCompact_lsup
          intro B hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
          exact hG D A (hlA D hD) hAff
        obtain ⟨l2, hl2, hs2⟩ := exists_cover _ hc
        apply stage1 P hA hS l2.length (lsup l ⊓ A).toScheme (l2.map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp)
          (good_affine A _ hAff inf_le_right)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (hl2 C hC).2 (hl2 C hC).1
        · rw [← preimage_lsup, hs2, Scheme.Opens.ι_preimage_self]

end ind

theorem ContInd_of : LateralTheory.E.ContPf.ContInd := by
  intro P hA hS X _ _
  have hc : IsCompact ((⊤ : X.Opens) : Set X) := by simpa using isCompact_univ
  obtain ⟨l, hl, hs⟩ := exists_cover (⊤ : X.Opens) hc
  refine stage2 P hA hS l.length X l rfl ?_ (fun B hB => (hl B hB).1) hs
  intro A B hA' hB'
  rw [TopologicalSpace.Opens.coe_inf]
  exact QuasiSeparatedSpace.inter_isCompact _ _ A.isOpen hA'.isCompact B.isOpen hB'.isCompact

end LateralTheory.E.ContIndPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.CoverPf

def EmptyVan : Prop := A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ) (S : Type) [CommRing S], Subsingleton S →
  ∀ x : Ht q (sp S) (n + 1) i, x = 0

theorem pull_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (q : ℕ) (m i : ℤ)
    (x : Ht q (sp A) m i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  have : spMap (g.comp f) = spMap g ≫ spMap f := by simp [spMap]
  rw [this, pull_comp]

theorem dies_of_factor {S : Type} [CommRing S] {q : ℕ} {m i : ℤ} (x : Ht q (sp S) m i) (f : S)
    (hx : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    {T : Type} [CommRing T] (φ : S →+* T) (hu : IsUnit (φ f)) : pull _ (spMap φ) _ _ x = 0 := by
  have e : φ = (IsLocalization.Away.lift f (S := Localization.Away f) hu).comp (algebraMap S (Localization.Away f)) :=
    (IsLocalization.Away.lift_comp f (S := Localization.Away f) hu).symm
  rw [e, pull_comp', hx, map_zero]

theorem dies_add (hQ : QAClosed) (hM : MV) (h1 : A1) {q : ℕ} {i n : ℤ} (hk : MVHyp q i n)
    {S : Type} [CommRing S] (hS : QA S) (hq : IsUnit (q : S)) (x : Ht q (sp S) (n + 1) i) (f g : S)
    (hf : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    (hg : pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0) :
    pull _ (spMap (algebraMap S (Localization.Away (f + g)))) _ _ x = 0 := by
  set T := Localization.Away (f + g)
  set φ := algebraMap S T
  have hT : QA T := (hQ S hS).2.1 (f + g)
  have hqT : IsUnit (q : T) := by simpa using hq.map φ
  have hspan : Ideal.span {φ f, φ g} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := T) (f + g)
    have hmem : φ (f + g) ∈ Ideal.span {φ f, φ g} := by
      rw [map_add]
      exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    have : (1 : T) = ((u⁻¹ : Tˣ) : T) * φ (f + g) := by
      change (1 : T) = ((u⁻¹ : Tˣ) : T) * algebraMap S T (f + g)
      rw [← hu]; simp
    rw [this]; exact Ideal.mul_mem_left _ _ hmem
  have key := hM h1 (ZMod q) (tw q i) T (φ f) (φ g) hspan n (hk T hT hqT (φ f) (φ g) hspan)
    (pull _ (spMap φ) _ _ x)
  apply key
  · rw [← pull_comp']
    exact dies_of_factor x f hf _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f)) (φ f))
  · rw [← pull_comp']
    exact dies_of_factor x g hg _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ g)) (φ g))

theorem Cover_of (hE : EmptyVan) : LateralTheory.E.AcycQAPf.Cover := by
  intro hQ hM h1 q _ i n hk S _ hS hq x hloc
  let I : Set S := {g | pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0}
  have hmul : ∀ a g, g ∈ I → a * g ∈ I := by
    intro a g hg
    refine dies_of_factor x g hg _ ?_
    exact isUnit_of_mul_isUnit_right (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a * g)) (a * g)
      |>.map (RingHom.id _) |> fun h => by simpa [map_mul] using h)
  have hadd : ∀ f g, f ∈ I → g ∈ I → f + g ∈ I := fun f g hf hg => dies_add hQ hM h1 hk hS hq x f g hf hg
  have hspan : Ideal.span I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM', hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hfM, hf⟩ := hloc ⟨M, hM'.isPrime⟩
    exact hfM (hle (Ideal.subset_span hf))
  have hP : ∀ y ∈ Ideal.span I, y ∈ I ∨ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Or.inl hy
    | zero => exact Or.inr rfl
    | add a b _ _ ha hb =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (hadd a b ha hb)
      · subst hb; simpa using Or.inl ha
      · subst ha; simpa using Or.inl hb
      · subst ha; subst hb; simp
    | smul a b _ hb =>
      rcases hb with hb | hb
      · exact Or.inl (hmul a b hb)
      · subst hb; simp
  rcases hP 1 (by rw [hspan]; trivial) with h | h
  · have := dies_of_factor x 1 h (RingHom.id S) isUnit_one
    have e : spMap (RingHom.id S) = 𝟙 _ := by simp [spMap]
    rwa [e, pull_id] at this
  · have : Subsingleton S := subsingleton_of_zero_eq_one h.symm
    exact hE h1 q i n S inferInstance x

end LateralTheory.E.CoverPf
end
end

