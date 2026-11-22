import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafHIPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafHIPf

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun y => ?_, fun y => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_isIso {R : Type} [CommRing R] {X Y : Scheme.{0}} (a : X ⟶ Y) [IsIso a] (F : Shv R) :
    Eqv R (sch.map a) F :=
  eqv_iso (sch.mapIso (asIso a)) F

theorem eqvS {R : Type} [CommRing R] {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (F : Shv R)
    (ha : Eqv R (sch.map a) F) (hb : Eqv R (sch.map b) F) : Eqv R (sch.map (a ≫ b)) F := by
  rw [Functor.map_comp]; exact eqv_comp _ _ F ha hb

def polyEquiv (A : Type) [CommRing A] : MvPolynomial (Fin 1) A ≃ₐ[A] Polynomial A :=
  MvPolynomial.uniqueAlgEquiv A (Fin 1)

theorem over_eq (A : Type) [CommRing A] :
    (𝔸(Fin 1; Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)) =
      ((AffineSpace.SpecIso (Fin 1) (CommRingCat.of A)).hom ≫
        Spec.map (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) := by
  have h := AffineSpace.SpecIso_inv_over (n := Fin 1) (CommRingCat.of A)
  have e : CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A) ≫
      CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom =
      CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg _ (RingHom.ext fun a => (polyEquiv A).symm.commutes a)
  rw [(Iso.inv_comp_eq _).1 h, Category.assoc, ← Spec.map_comp]
  erw [e]

theorem step {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : Type) [CommRing A]
    (s : Spec (CommRingCat.of A) ⟶ X) (k : 𝔸(Fin 1; X) ⟶ X) (hk : k = 𝔸(Fin 1; X) ↘ X)
    (g : pullback k s ⟶ pullback (𝟙 X) s) (hg : g ≫ pullback.snd _ _ = pullback.snd _ _)
    (hC : Eqv R (spMap (Polynomial.C : A →+* Polynomial A)) F) : Eqv R (sch.map g) F := by
  subst hk
  have P := AffineSpace.isPullback_map (n := Fin 1) s
  have hsnd : pullback.snd (𝔸(Fin 1; X) ↘ X) s = P.isoPullback.inv ≫ (((AffineSpace.SpecIso (Fin 1) (CommRingCat.of A)).hom ≫
        Spec.map (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) :=
    ((Iso.eq_inv_comp _).2 P.isoPullback_hom_snd).trans (congrArg (P.isoPullback.inv ≫ ·) (over_eq A))
  have hgeq : g = pullback.snd (𝔸(Fin 1; X) ↘ X) s ≫ inv (pullback.snd (𝟙 X) s) := by
    rw [← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hI : IsIso (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom) :=
    (polyEquiv A).symm.toRingEquiv.toCommRingCatIso.isIso_hom
  rw [hgeq, hsnd]
  exact eqvS _ _ F (eqvS _ _ F (eqv_isIso _ F) (eqvS _ _ F (eqvS _ _ F (eqv_isIso _ F) (eqv_isIso _ F)) hC))
    (eqv_isIso _ F)

theorem LeafHI_of : LateralTheory.E.t_E6Cut.LeafHI := by
  intro b3 c4 q _ i X hq
  refine b3 q (𝔸(Fin 1; X) ↘ X) (𝟙 X) hq i (fun A _ s _ => ?_)
  have hqA : IsUnit (q : A) := by
    simpa using hq.map (s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom
  exact step _ X A s _ (Category.comp_id _) _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) (c4 q A hqA i)

end LateralTheory.E.LeafHIPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKillCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKillCut

open LateralTheory.E.E4

def LeafOne : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → ∀ x : Ht q (sch.obj C) m i,
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m x = 0

theorem goal_of (hOne : LeafOne) : LateralTheory.E.E4.LeafKill := by
  intro hy q _ Ω _ _ hq C c hc m i hm hfin
  classical
  have key : ∀ s : Finset (Ht q (sch.obj C) m i), ∃ (C' : Scheme.{0}) (γ : C' ⟶ C),
      IsCurve (γ ≫ c) ∧ Surjective γ ∧ ∀ x ∈ s, pl q i γ m x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C, 𝟙 C, by simpa using hc, inferInstance, by simp⟩
    | insert a s ha IH =>
      obtain ⟨C1, γ1, h1, s1, k1⟩ := IH
      obtain ⟨C2, γ2, h2, s2, k2⟩ := hOne hy q Ω hq (γ1 ≫ c) h1 m i hm (pl q i γ1 m a)
      have := s1
      have := s2
      refine ⟨C2, γ2 ≫ γ1, by simpa [Category.assoc] using h2, inferInstance, ?_⟩
      intro x hx
      rw [pl_comp]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact k2
      · rw [k1 x hx, map_zero]
  have := Fintype.ofFinite (Ht q (sch.obj C) m i)
  obtain ⟨C', γ, h1, h2, h3⟩ := key Finset.univ
  exact ⟨C', γ, h1, h2, AddMonoidHom.ext fun x => by simpa using h3 x (Finset.mem_univ x)⟩

end LateralTheory.E.LeafKillCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKumCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafKumCut

def LeafTwist : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nonempty (Prim q B) →
  ∀ n i j : ℤ, Nonempty (Ht q (sp B) n i ≃+ Ht q (sp B) n j)

def EtaleFirstCohomologyMultiplicativeGroupPicard : Prop := Hyps → DivisorPicardCompatibility

def LeafKumSeq : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ (a : Additive (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) →+ Ht q (sp B) 1 1)
    (b : Ht q (sp B) 1 1 →+ H ℤ (sp B) Gm 1), Function.Exact a b

theorem prim_of_isAlgClosed (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k)) :
    Nonempty (Prim q k) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)))
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem finite_of_exact {A M N : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup N] [Finite A]
    (a : A →+ M) (b : M →+ N) (h : Function.Exact a b) (hb : Finite b.range) : Finite M := by
  have hK : Finite b.ker := by
    have : (b.ker : Set M) = Set.range a := by ext x; exact h x
    have hf : (Set.range a).Finite := Set.finite_range a
    rw [← this] at hf
    exact hf.to_subtype
  have hQ : Finite (M ⧸ b.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange b).symm.toEquiv
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup b.ker
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  have : Nonempty (M ⧸ b.ker) := ⟨0⟩
  exact Nat.mul_ne_zero (Nat.card_pos).ne' (Nat.card_pos).ne'

theorem goal_of (hT : LeafTwist) (hG : EtaleFirstCohomologyMultiplicativeGroupPicard) (hS : LeafKumSeq) : LeafKum := by
  intro hy q _ k B _ _ _ _ hq hU hP i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨ζ⟩ := prim_of_isAlgClosed q k hq
  obtain ⟨e⟩ := hT hy q B ⟨ζ.map (algebraMap k B)⟩ 1 i 1
  obtain ⟨a, b, hab⟩ := hS hy q B hqB
  obtain ⟨E⟩ := hG hy B
  have hr : Finite b.range := by
    refine Finite.of_injective (β := {c : CommRing.Pic B // c ^ q = 1})
      (fun y => ⟨Additive.toMul (E y.1), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      have h0 : q • x = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]
      have : q • E y.1 = 0 := by rw [← hx, ← map_nsmul, ← map_nsmul, h0, map_zero, map_zero]
      rw [← toMul_nsmul, this, toMul_zero]
    · intro y z h
      apply Subtype.ext
      apply E.injective
      apply Additive.toMul.injective
      exact congrArg Subtype.val h
  have : Finite (Ht q (sp B) 1 1) := finite_of_exact a b hab hr
  exact Finite.of_equiv _ e.symm.toEquiv

end LateralTheory.E.LeafKumCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKunnethCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKunnethCut

def KBasis (q : ℕ) {Y : Scheme.{0}} (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ) (b : ∀ s, Ht q (sch.obj Y) (deg s) j) :
    Prop :=
  ∀ m : ℤ, Function.Bijective fun c : {s // deg s = m} → ZMod q =>
    ∑ s : {s // deg s = m}, c s • ((b s.1).cast s.2 rfl : Ht q (sch.obj Y) m j)

def KunAt (q : ℕ) {k : Type} [Field k] {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (r : Y ⟶ Spec (CommRingCat.of k)) (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j) : Prop :=
  ∀ n i : ℤ, Function.Bijective fun a : ∀ s, Ht q (sch.obj X) (n - deg s) i =>
    ∑ s, ((cup q (pull _ (sch.map (pullback.fst p r)) _ _ (a s)) (pull _ (sch.map (pullback.snd p r)) _ _ (b s))).cast
      (by ring) rfl : Ht q (sch.obj (pullback p r)) n (i + j))

def LeafSHCoh : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ (A : Type) [CommRing A], SH A → ∀ (_s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k)) (i : ℤ),
    (∃ g : Ht q (sch.obj (Spec (CommRingCat.of A))) 0 i, Function.Bijective fun c : ZMod q => c • g) ∧
    ∀ n : ℤ, n ≠ 0 → Subsingleton (Ht q (sch.obj (Spec (CommRingCat.of A))) n i)

def LeafKunLocal : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j), KBasis q S deg j b →
  ∀ (A : Type) [CommRing A], SH A → ∀ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k), KunAt q s r S deg j b

def LeafKunGlobal : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j), KBasis q S deg j b →
  (∀ (A : Type) [CommRing A], SH A → ∀ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k), KunAt q s r S deg j b) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact p] [QuasiSeparated p], KunAt q p r S deg j b

theorem goal_of (hL : LeafKunLocal) (hG : LeafKunGlobal) : LateralTheory.E.E8.EtaleKunneth := by
  intro hB q _ k _ _ hq X Y p r _ _ _ _ S _ deg j b hb
  exact hG hB q k hq r S deg j b hb (hL hB q k hq r S deg j b hb) p

end LateralTheory.E.LeafKunnethCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLinePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafLinePf

theorem det_mulVec_one (A : Type) [CommRing A] (g : GL (Fin 1) A) :
    (g : Matrix (Fin 1) (Fin 1) A).mulVec (fun _ => 1) = ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) • (fun _ => (1 : A)) := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, Matrix.det_unique]

def e1 (A : Type) [CommRing A] : Um 1 A := ⟨fun _ => 1, by
  rw [Set.range_const]; exact Ideal.span_singleton_one⟩

def secF (A : Type) [CommRing A] : SingleObj (GL (Fin 1) A) ⥤ Um 1 A where
  obj _ := e1 A
  map g := ⟨(g, Matrix.GeneralLinearGroup.det g), det_mulVec_one A g⟩
  map_id _ := Subtype.ext (Prod.ext rfl (map_one _))
  map_comp f g := Subtype.ext (Prod.ext rfl (map_mul _ _ _))

theorem eqToHom_val {A : Type} [CommRing A] {v w : Um 1 A} (h : v = w) : (eqToHom h).1 = 1 := by
  cases h; rfl

theorem comp_val {A : Type} [CommRing A] {u v w : Um 1 A} (a : u ⟶ v) (b : v ⟶ w) : (a ≫ b).1 = b.1 * a.1 := rfl

theorem det_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 1) A) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g) : Bˣ) : B) = f ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.map_det]
  rfl

def secNat : glCat 1 ⟶ pglCat 1 where
  app A := (secF A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => Subtype.ext (funext fun _ => (map_one f.hom).symm)) (fun _ _ g => ?_)
    apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val, one_mul, mul_one]
    refine Prod.ext rfl ?_
    ext
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.hom (show GL (Fin 1) A from g)) : (B : Type)ˣ) : (B : Type)) =
      f.hom ((Matrix.GeneralLinearGroup.det (show GL (Fin 1) A from g) : (A : Type)ˣ) : (A : Type))
    exact det_map f.hom _

theorem ofCatMap_comp {C D F : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) (β : D ⟶ F) :
    ofCatMap α ≫ ofCatMap β = ofCatMap (α ≫ β) := rfl

theorem ofCatMap_id (C : CommRingCat.{0} ⥤ Cat.{0,0}) : ofCatMap (𝟙 C) = 𝟙 _ := rfl

def sec : ofCat (glCat 1) ⟶ PGL 1 := ofCatMap secNat

theorem sec_pr : sec ≫ PGL.pr 1 = 𝟙 (ofCat (glCat 1)) := rfl

theorem single_eqToHom {M : Type} [Monoid M] {x y : SingleObj M} (h : x = y) : (eqToHom h : x ⟶ y) = (1 : M) := by
  cases h; rfl

theorem sec_line : sec ≫ PGL.line 1 = 𝟙 (ofCat (glCat 1)) := by
  rw [sec, PGL.line]
  erw [ofCatMap_comp]
  rw [← ofCatMap_id]
  congr 1
  apply NatTrans.ext
  funext A
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ g => ?_)
  erw [single_eqToHom]
  change _ = ((1 : GL (Fin 1) A) * (id g : GL (Fin 1) A)) * 1
  rw [one_mul, mul_one]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det (id g : GL (Fin 1) A)) = (id g : GL (Fin 1) A)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

end LateralTheory.E.LeafLinePf

namespace LateralTheory.E.D2
open LateralTheory.E.LeafLinePf

theorem LeafLine_of (hA : LeafA6nat) : LeafLine := by
  intro q _ P E h L c hc
  obtain ⟨h0, -, heq⟩ := hc
  have hw : 𝟙 E ≫ L = (L ≫ sec) ≫ PGL.pr 1 := by
    rw [Category.assoc, sec_pr, Category.id_comp, Category.comp_id]
  let σ : E ⟶ PB L := pullback.lift (𝟙 E) (L ≫ sec) hw
  have hpr : σ ≫ PB.pr L = 𝟙 E := pullback.lift_fst _ _ _
  have hline : σ ≫ PB.line L = L := by
    rw [PB.line, ← Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.assoc, sec_line, Category.comp_id]
  have h' : Inv q (PB L) := inv_of (PB.pr L) h
  have hm : ∀ j, P.map σ h h' (P.map (PB.pr L) h' h (P.ι h j (c j))) = P.ι h j (c j) := by
    intro j
    rw [P.map_ι, P.map_ι, ← pull_comp, hpr, pull_id]
  have hx : P.map σ h h' (P.deg1 h' (c1 q (PB.line L))) = P.deg1 h (c1 q L) := by
    rw [Collected.deg1, P.map_ι, pull_cast, (hA q).2.2.1 σ (PB.line L) h', hline]
  have := congrArg (P.map σ h h') heq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_mul, map_pow, map_zero, zero_add, hm, hx,
    map_one, h0] at this
  simp only [one_mul, Nat.sub_zero, Nat.sub_self, pow_one, pow_zero, mul_one] at this
  linear_combination this

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNatPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem pull_cast_nat {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn hi; rfl

abbrev PB.over {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) : PB (f ≫ V) ⟶ PB V :=
  pullback.map (f ≫ V) (PGL.pr N) V (PGL.pr N) f (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem PB.over_pr {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.pr V = PB.pr (f ≫ V) ≫ f := by
  simp only [PB.over, PB.pr, pullback.map, pullback.lift_fst]

theorem PB.over_line {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.line V = PB.line (f ≫ V) := by
  simp only [PB.over, PB.line, pullback.map, pullback.lift_snd_assoc, Category.comp_id]

theorem LeafNat_of (hA : LeafA6nat) : LeafNat := by
  intro q _ P E E' f h h' N V c hc
  obtain ⟨h0, hz, hs⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [← P.map_ι f h h', h0, map_one]
  · intro j hj; simp [hz j hj]
  · have hg := congrArg (P.map (PB.over f V) (inv_of (PB.pr (f ≫ V)) h) (inv_of (PB.pr V) h')) hs
    rw [map_zero, map_sum] at hg
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, P.map_ι, Collected.deg1, pull_cast_nat, ← pull_comp, PB.over_pr]
    rw [(hA q).2.2.1 _ _ (inv_of (PB.pr V) h'), PB.over_line]

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNewtonPf
section
noncomputable section
open PowerSeries

namespace LateralTheory.E.LeafNewtonPf

def nser {A : Type 1} [CommRing A] (c : ℕ → A) : PowerSeries A :=
  -(X * derivative A (mk c)) * (mk c).invOfUnit 1

lemma uniq {A : Type 1} [CommRing A] {f g s : PowerSeries A} (hf : constantCoeff f = 1) (h : s * f = g) :
    g * f.invOfUnit 1 = s := by
  rw [← h, mul_assoc, mul_invOfUnit f 1 (by simp [hf]), mul_one]

lemma nser_eq {A : Type 1} [CommRing A] (c : ℕ → A) {s : PowerSeries A} (h0 : constantCoeff (mk c) = 1)
    (h : s * mk c = -(X * derivative A (mk c))) : nser c = s := uniq h0 h

lemma nser_spec {A : Type 1} [CommRing A] (c : ℕ → A) (h0 : c 0 = 1) :
    nser c * mk c = -(X * derivative A (mk c)) := by
  unfold nser
  rw [mul_assoc, invOfUnit_mul (mk c) 1 (by simp [h0]), mul_one]

lemma map_deriv {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (f : PowerSeries A) :
    map φ (derivative A f) = derivative B (map φ f) := by
  ext n
  simp [coeff_derivative, coeff_map, map_mul, map_natCast]

lemma part1 {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A) (h0 : c 0 = 1) (k : ℕ) :
    φ (LateralTheory.E.D2.newton c k) = LateralTheory.E.D2.newton (fun j => φ (c j)) k := by
  have hm : map φ (mk c) = mk (fun j => φ (c j)) := by ext n; simp [coeff_map]
  have key : nser (fun j => φ (c j)) = map φ (nser c) := by
    apply nser_eq _ (by simp [h0])
    have := congrArg (map φ) (nser_spec c h0)
    rw [map_mul, hm, map_neg, map_mul, map_X, map_deriv, hm] at this
    exact this
  show φ (coeff k (nser c)) = coeff k (nser (fun j => φ (c j)))
  rw [key, coeff_map]

lemma part2 {A : Type 1} [CommRing A] (c d e : ℕ → A) (hc : c 0 = 1) (hd : d 0 = 1)
    (he : ∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) (k : ℕ) :
    LateralTheory.E.D2.newton e k = LateralTheory.E.D2.newton c k + LateralTheory.E.D2.newton d k := by
  have hm : mk e = mk c * mk d := by ext n; rw [coeff_mk, he, coeff_mul]; simp [coeff_mk]
  have he0 : e 0 = 1 := by rw [he]; simp [hc, hd]
  have key : nser e = nser c + nser d := by
    apply nser_eq _ (by simp [he0])
    rw [hm, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 := nser_spec c hc
    have h2 := nser_spec d hd
    linear_combination (mk d) * h1 + (mk c) * h2
  show coeff k (nser e) = coeff k (nser c) + coeff k (nser d)
  rw [key, map_add]

lemma geom {A : Type 1} [CommRing A] (x : A) : mk (fun k => x ^ k) * (1 - C x * X) = 1 := by
  ext n
  rcases n with _ | n
  · simp [mul_sub]
  · rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm _ (C x), coeff_succ_mul_X, coeff_C_mul]
    simp [pow_succ, mul_comm]

lemma part3 {A : Type 1} [CommRing A] (c : ℕ → A) (x : A) (h0 : c 0 = 1) (h1 : c 1 = -x)
    (h2 : ∀ j, 1 < j → c j = 0) (k : ℕ) (hk : 0 < k) : LateralTheory.E.D2.newton c k = x ^ k := by
  have hm : mk c = 1 - C x * X := by
    ext n
    rcases n with _ | _ | n
    · simp [h0]
    · simp [h1]
    · rw [coeff_mk, h2 _ (by omega)]
      simp [coeff_one]
  have key : nser c = C x * X * mk (fun k => x ^ k) := by
    apply nser_eq _ (by simp [h0])
    rw [mul_assoc, hm, geom, mul_one]
    simp [map_sub, mul_comm]
  show coeff k (nser c) = x ^ k
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [key, mul_comm (C x) X, mul_assoc, coeff_succ_X_mul, coeff_C_mul, coeff_mk, pow_succ, mul_comm]

theorem LeafNewton_of : LateralTheory.E.D2.LeafNewton :=
  ⟨fun _ _ _ _ φ c h0 k => part1 φ c h0 k,
   fun _ _ c d e hc hd he k => part2 c d e hc hd he k,
   fun _ _ c x h0 h1 h2 k hk => part3 c x h0 h1 h2 k hk⟩

end LateralTheory.E.LeafNewtonPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSupport
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafA6suppPf

def LeafAWSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
  (α : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n)
  (β : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q j)) m),
  ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q (i + j))) (n + m),
    (twPair q i j).IsAW rfl α.1 β.1 γ.1 ∧
    cup q (CohomologyClass.mk α : Ht q E n i) (CohomologyClass.mk β : Ht q E m j) = CohomologyClass.mk γ

def LeafRepVanish : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ (F : Shv R) (n : ℤ)
  (a : H R E F n), pull R f F n a = 0 →
  ∃ α : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk α = a ∧
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y), ev α.1 N w h Y ((f.app _).app _ y) = 0

def LeafCochainVanish : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ (K : Cx R) (k : ℤ) (γ : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0) →
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) →
    γ = 0

theorem sub_map {U E : Spc} (f : U ⟶ E) {N : ℕ} {Y : Scheme.{0}} (y : Sx U N Y) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((f.app _).app _ y) j l h = (f.app _).app _ (Sx.sub y j l h) := by
  unfold Sx.sub
  have e := NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op Y)
  exact (ConcreteCategory.congr_hom e y).symm

theorem LeafA6supp_of (h1 : LeafAWSpec) (h2 : LeafRepVanish) (h3 : LeafCochainVanish) : LateralTheory.E.D2.LeafA6supp := by
  intro q _ U V E f g hc n m i j a b ha hb
  obtain ⟨α, rfl, hα⟩ := h2 (ZMod q) f hc.1 (tw q i) n a ha
  obtain ⟨β, rfl, hβ⟩ := h2 (ZMod q) g hc.2.1 (tw q j) m b hb
  obtain ⟨γ, hAW, hcup⟩ := h1 q E α β
  rw [hcup]
  have : γ.1 = 0 := by
    apply h3 (ZMod q) f g hc
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map f y 0 (p : ℕ), hα]
      simp
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map g y (p : ℕ) (N - p), hβ]
      simp
  have hγ : γ = 0 := Subtype.ext this
  rw [hγ]
  exact CohomologyClass.mk_zero _ _ _

end LateralTheory.E.LeafA6suppPf
end
end

