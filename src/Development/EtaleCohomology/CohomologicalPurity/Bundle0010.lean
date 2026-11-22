import Development.EtaleCohomology.CohomologicalPurity.LeafThomCutDef
import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafThomCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafGeo : Prop :=
  (∀ (d : ℕ) (R : Type) [CommRing R], Mono (pr d R).hom) ∧
  (∀ (q N k : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → Inv q (PR N k R)) ∧
  (∀ (d : ℕ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A),
    spMap φ ≫ Pj.pt (vec1 x) = Pj.pt (vec1 (φ ∘ x))) ∧
  ∀ (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A), Ideal.span (Set.range x) = I →
    ∃ Φ : opn (off A I) ⟶ pr d A, Φ.right = chart x

def LeafAct : Prop := ∀ (d : ℕ) (A : Type) [CommRing A] (M : Matrix (Fin d) (Fin d) A), IsUnit M.det →
  ∃ g : pr d A ⟶ pr d A,
    (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) ≫ prod.fst ≫ Pj.line (d + 1) 0 = prod.fst ≫ Pj.line (d + 1) 0 ∧
    (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) ≫ prod.snd = prod.snd ∧
    ∀ x : Fin d → A, chart x ≫ (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) = chart (M.mulVec x)

def LeafPB : Prop := A1 → DivisorNaturality → D1 → ∀ (q : ℕ) [NeZero q] (N : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∀ n i : ℤ, Function.Bijective (poly q N 0 R N n i)

def LeafHtpy : Prop := A1 → A4 → C4 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), I.FG → IsUnit (q : A) →
  ∀ (h : off (Polynomial A) (I.map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafTail : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ i : ℤ,
  Eqv _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) (tw q i)

def LeafTau : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  (∃! τ, IsTau q d R τ) ∧ ∀ τ, IsTau q d R τ → ∀ n i : ℤ, Function.Bijective fun a : Ht q (sp R) n i =>
    Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ a) τ

def LeafTauNat : Prop := DivisorNaturality → A11 → ∀ (q : ℕ) [NeZero q] (d : ℕ) (A : Type) [CommRing A], IsUnit (q : A) →
  ∀ τ, IsTau q d A τ →
  (∀ (B : Type) [CommRing B] (φ : A →+* B) (g : pr d B ⟶ pr d A),
    (g.right : PR (d + 1) 0 B ⟶ PR (d + 1) 0 A) ≫ prod.fst ≫ Pj.line (d + 1) 0 = prod.fst ≫ Pj.line (d + 1) 0 →
    (g.right : PR (d + 1) 0 B ⟶ PR (d + 1) 0 A) ≫ prod.snd = prod.snd ≫ spMap φ → IsTau q d B (Hs.pull q g _ _ τ)) ∧
  ∀ r : ℕ, r ∣ q → ∀ τ' : Hs r (pr d A) (2 * d) d, τ'.1 = red q r _ _ _ τ.1 → IsTau r d A τ'

def LeafExcSp : Prop := A1 → ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → Exc q φ

def LeafExcP : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) → ∀ Φ : opn (off (MvPolynomial (Fin d) R) I) ⟶ pr d R,
  Φ.right = (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
    sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) → Exc q Φ

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P := pushout.inl_desc _ _ _

theorem inl_fold (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc _ _ _

theorem map_comp {P'' P' P : Arrow Spc} (ψ : P'' ⟶ P') (φ : P' ⟶ P) : dbl.map (ψ ≫ φ) = dbl.map ψ ≫ dbl.map φ := by
  refine pushout.hom_ext ?_ ?_
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, Arrow.comp_right, Category.assoc]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  refine pushout.hom_ext ?_ ?_
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [← Category.assoc, inl_map, Category.assoc, inl_fold, ← Category.assoc, inl_fold, Category.comp_id, Category.id_comp]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_fold, ← Category.assoc, dbl.inr_fold, Category.comp_id,
      Category.id_comp]

theorem hs_comp (q : ℕ) {P'' P' P : Arrow Spc} (ψ : P'' ⟶ P') (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q ψ n i (Hs.pull q φ n i x) = Hs.pull q (ψ ≫ φ) n i x :=
  Subtype.ext (by
    change pull _ (dbl.map ψ) _ n (pull _ (dbl.map φ) _ n x.1) = pull _ (dbl.map (ψ ≫ φ)) _ n x.1
    rw [map_comp, pull_comp])

theorem hs_act (h : DivisorNaturality) (q : ℕ) [NeZero q] {P' P : Arrow Spc} (φ : P' ⟶ P) {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : Hs.pull q φ _ _ (Hs.act q a b) = Hs.act q (pull _ φ.right _ _ a) (Hs.pull q φ _ _ b) :=
  Subtype.ext (by
    have e : cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a)) (pull _ (dbl.map φ) _ m b.1) =
        pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1) := by
      rw [(h q).1, ← pull_comp, ← pull_comp, map_fold]
    change pull _ (dbl.map φ) _ _ (_ - _) = cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a))
      (pull _ (dbl.map φ) _ m b.1) - pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a)) (pull _ (dbl.map φ) _ m b.1)))
    rw [e, map_sub, ← pull_comp _ (dbl.inr P'), dbl.inr_map, pull_comp, ← pull_comp _ (dbl.fold P'), ← map_fold, pull_comp])

theorem hom_ext {P' P : Arrow Spc} (h : Mono P.hom) {φ ψ : P' ⟶ P} (e : φ.right = ψ.right) : φ = ψ := by
  refine Arrow.hom_ext _ _ ?_ e
  rw [← cancel_mono P.hom, Arrow.w, Arrow.w, e]

theorem goal_of (hG : LeafGeo) (hA : LeafAct) (hT : LeafTau) (hN : LeafTauNat) (hE : LeafExcP) : LeafThom := by
  intro H d
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have h11 : A11 := H.2.2.2.2.2.2.2.1
  obtain ⟨hm, -, hpt, hΦ⟩ := hG
  choose Φ hΦ using hΦ d
  let τ : ∀ (q : ℕ) (A : Type) [CommRing A], Hs q (pr d A) (2 * d) d := fun q A _ => pick (IsTau q d A)
  have hτ : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → IsTau q d A (τ q A) :=
    fun q _ A _ hq => pick_spec (hT H q d A hq).1.exists
  have huq : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ t, IsTau q d A t → t = τ q A :=
    fun q _ A _ hq t ht => (hT H q d A hq).1.unique ht (hτ q A hq)
  have hb : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), IsUnit (q : A) →
      Hs.pull q (prMap d φ) _ _ (τ q A) = τ q B := fun q _ A B _ _ φ hq =>
    huq q B (by simpa using hq.map φ) _ ((hN h6 h11 q d A hq _ (hτ q A hq)).1 B φ _
      ((prod.map_fst_assoc (𝟙 (Pj (d + 1) 0)) (spMap φ) (Pj.line (d + 1) 0)).trans
        (congrArg (fun f => prod.fst ≫ f) (Category.id_comp _)))
      (prod.map_snd _ _))
  refine ⟨fun q A _ I x hx => Hs.pull q (Φ A I x hx) _ _ (τ q A), fun q _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro A B _ _ φ I J x hx hy h hq
    have e : opnMap (Spec.map (CommRingCat.ofHom φ)) (off B J) (off A I) h ≫ Φ A I x hx = Φ B J _ hy ≫ prMap d φ := by
      refine hom_ext (hm d A) ?_
      rw [Arrow.comp_right, Arrow.comp_right, hΦ, hΦ]
      change spMap φ ≫ chart x = chart (φ ∘ x) ≫ prod.map (𝟙 _) (spMap φ)
      rw [chart, chart, prod.comp_lift, prod.lift_map, hpt, Category.comp_id, Category.comp_id, Category.id_comp]
    beta_reduce
    rw [hs_comp, e, ← hs_comp, hb q A B φ hq]
  · intro A _ I x M hx hy hq hM
    obtain ⟨g, g1, g2, g3⟩ := hA d A M hM
    have e : Φ A I _ hy = Φ A I x hx ≫ g := by
      refine hom_ext (hm d A) ?_
      rw [Arrow.comp_right, hΦ, hΦ]
      exact (g3 x).symm
    have e2 : Hs.pull q g _ _ (τ q A) = τ q A := huq q A hq _ ((hN h6 h11 q d A hq _ (hτ q A hq)).1 A (RingHom.id A) g g1
      (by
        have : spMap (RingHom.id A) = 𝟙 _ := by
          change sch.map (Spec.map (𝟙 _)) = _
          rw [Spec.map_id, CategoryTheory.Functor.map_id]
        rw [this, Category.comp_id]
        exact g2))
    beta_reduce
    rw [e, ← hs_comp, e2]
  · intro R _ I hx hq n i
    have er : (Φ _ I MvPolynomial.X hx ≫ prMap d (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)).right =
        (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
          sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) := by
      rw [Arrow.comp_right, hΦ]
      change chart _ ≫ prod.map (𝟙 _) (spMap _) = _
      rw [chart, prod.lift_map, Category.comp_id, Category.id_comp]
    have hb2 := (hE H q d R I hx hq _ er _ _).comp ((hT H q d R hq).2 _ (hτ q R hq) n i)
    convert hb2 using 1
    funext a
    refine Eq.symm ((hs_act h6 q _ _ _).trans (congrArg₂ (Hs.act q) ?_ ?_))
    · refine (congrArg (fun f => pull _ f _ n (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ n a)) er).trans ?_
      exact (pull_comp _ _ _ _ _ _).symm.trans (congrArg (fun f => pull _ f _ n a) (prod.lift_snd _ _))
    · exact (hs_comp q _ _ _ _ _).symm.trans (congrArg _ (hb q R _ _ hq))
  · intro r hr A _ I x hx hq
    have : NeZero r := ⟨fun h => NeZero.ne q (by simpa [h] using hr)⟩
    have hr' : IsUnit (r : A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hr) hq
    have hmem : red q r _ _ _ (τ q A).1 ∈ Hs r (pr d A) (2 * d) d := by
      change pull _ (dbl.inr _) _ _ _ = 0
      have h0 : pull _ (dbl.inr (pr d A)) (tw q d) (2 * d) (τ q A).1 = 0 := (τ q A).2
      rw [pull_red, h0, map_zero]
    have e := huq r A hr' _ ((hN h6 h11 q d A hq _ (hτ q A hq)).2 r hr ⟨_, hmem⟩ rfl)
    change pull _ (dbl.map _) _ _ (τ r A).1 = red q r _ _ _ (pull _ (dbl.map _) _ _ (τ q A).1)
    rw [← e]
    exact pull_red _ _ _ _ _ _

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafVanRingPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl

theorem sub_C_mem_X {σ R : Type} [CommRing R] (f : MvPolynomial σ R) :
    f - MvPolynomial.C (MvPolynomial.constantCoeff f) ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    have : p + r - MvPolynomial.C (MvPolynomial.constantCoeff (p + r)) =
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) + (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p n _ =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, rfl⟩)

theorem chart_nbhd {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (φ : A →+* B)
    (ψ : MvPolynomial (Fin d) (A ⧸ I) →+* B) (hφ : Nbhd φ I) (hψ : ψ.Etale)
    (hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ)
    (hc : ∀ a : A, φ a - ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) ∈ I.map φ) :
    Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) := by
  refine ⟨hψ, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hJ] at hf
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.constantCoeff f)
    have h1 : ψ (f - MvPolynomial.C (MvPolynomial.constantCoeff f)) ∈ I.map φ := by
      rw [← hJ]; exact Ideal.mem_map_of_mem _ (sub_C_mem_X f)
    have h2 : φ a ∈ I.map φ := by
      have := sub_mem (add_mem (hc a) (sub_mem hf h1)) (0 : I.map φ).2
      rw [map_sub, ← ha] at this
      simpa using this
    have h3 : Ideal.Quotient.mk I a = 0 := by
      apply hφ.2.1
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact h2
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := sub_C_mem_X f
    rwa [← ha, h3, map_zero, sub_zero] at this
  · intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', ha'⟩ := hφ.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk I a)), ?_⟩
    rw [Ideal.quotientMap_mk] at ha' ⊢
    rw [Ideal.Quotient.eq] at ha' ⊢
    rw [hJ]
    have := sub_mem ha' (hc a)
    simpa using this

theorem LeafVanRing_of (hNb : LeafNb) (hTh : LeafThom) : LeafVanRing := by
  intro hH d q _ A _ I hC hq n i hn
  have hA1 : A1 := hH.1
  have hA9 : A9 := hH.2.2.2.2.2.2.1
  obtain ⟨B, _, φ, ψ, hφ, hψ, hI, hc⟩ := hC
  have hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ := by
    rw [Ideal.map_span, hI, ← Set.range_comp]; rfl
  have hN := chart_nbhd I φ ψ hφ hψ hJ hc
  have e1 := hNb hA1 q φ I (I.map φ) hφ rfl (off_map φ I).le n i
  have e2 := hNb hA1 q ψ _ _ hN rfl (off_map ψ _).le n i
  obtain ⟨th, hth⟩ := hTh hH d
  have hqR : IsUnit (q : A ⧸ I) := by simpa using hq.map (Ideal.Quotient.mk I)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * d := ⟨n - 2 * d, by ring⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  have hm : m < 0 := by omega
  have hsub : Subsingleton (Ht q (sp (A ⧸ I)) m j) := (hA9 (ZMod q) (tw q j)).1 _ m hm
  have h3 := ((hth q).2.2.1 (A ⧸ I) _ rfl hqR m j).2
  have hR : Subsingleton (Hs q (opn (off (MvPolynomial (Fin d) (A ⧸ I))
      (Ideal.span (Set.range MvPolynomial.X)))) (m + 2 * d) (j + d)) := by
    constructor; intro x y
    obtain ⟨a, rfl⟩ := h3 x; obtain ⟨b, rfl⟩ := h3 y; rw [Subsingleton.elim a b]
  have hB : ∀ x y : Hs q (opn (off B ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ))) (m + 2 * d) (j + d), x = y := by
    intro x y
    obtain ⟨a, rfl⟩ := e2.2 x; obtain ⟨b, rfl⟩ := e2.2 y; rw [Subsingleton.elim a b]
  rw [hJ] at hB
  exact ⟨fun x y => e1.1 (hB _ _)⟩

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafZornPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.ZornPf
open LateralTheory.CohomologicalPurity.Cl

theorem rs_rs {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V W : X.Opens} (h1 : U ≤ V) (h2 : V ≤ W)
    (a : Sec G W.toScheme) : rs h1 (rs h2 a) = rs (h1.trans h2) a := by
  change (G.obj.map (X.homOfLE h1).op).hom ((G.obj.map (X.homOfLE h2).op).hom a) = (G.obj.map (X.homOfLE _).op).hom a
  rw [← Scheme.homOfLE_homOfLE X h1 h2, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem rs_refl {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U)
    (a : Sec G U.toScheme) : rs h a = a := by
  change (G.obj.map (X.homOfLE h).op).hom a = a
  rw [Scheme.homOfLE_rfl X U]
  simp

theorem rs_sub {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V)
    (a b : Sec G V.toScheme) : rs h (a - b) = rs h a - rs h b := map_sub _ _ _

theorem rs_add {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V)
    (a b : Sec G V.toScheme) : rs h (a + b) = rs h a + rs h b := map_add _ _ _

theorem glue {R : Type} [CommRing R] (G : Shv R) {X : Scheme.{0}} {A : Type*} (V : A → X.Opens)
    (s : ∀ k, Sec G (V k).toScheme) (hc : ∀ k l, rs inf_le_left (s k) = rs inf_le_right (s l)) :
    ∃ c : Sec G (⨆ k, V k).toScheme, ∀ k, rs (le_iSup V k) c = s k := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond
  have hmem : Sieve.generate (Presieve.ofArrows (fun k => (V k).toScheme) (fun k => X.homOfLE (le_iSup V k)))
      ∈ Scheme.etaleTopology (⨆ k, V k).toScheme := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : (x.1 : X) ∈ ⨆ k, V k := x.2
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨k, hk⟩ := hx
      refine ⟨k, ⟨⟨x.1, hk⟩, ?_⟩⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply (le_iSup V k) ⟨x.1, hk⟩
    · infer_instance
  have hS := hG.isSheafFor _ hmem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨c, hc', -⟩ := hS s (by
    intro i j Z gi gj e
    have e' : gi ≫ (V i).ι = gj ≫ (V j).ι := by
      have := congrArg (· ≫ (⨆ k, V k).ι) e
      simpa using this
    have hr : Set.range (gi ≫ (V i).ι) ⊆ Set.range (V i ⊓ V j).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, ?_⟩
      · have : (gi ≫ (V i).ι) z ∈ Set.range (V i).ι := ⟨gi z, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      · rw [e']
        have : (gj ≫ (V j).ι) z ∈ Set.range (V j).ι := ⟨gj z, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
    let l := IsOpenImmersion.lift (V i ⊓ V j).ι (gi ≫ (V i).ι) hr
    have hl : l ≫ (V i ⊓ V j).ι = gi ≫ (V i).ι := IsOpenImmersion.lift_fac _ _ _
    have li : gi = l ≫ X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) := by
      rw [← cancel_mono (V i).ι, Category.assoc, Scheme.homOfLE_ι, hl]
    have lj : gj = l ≫ X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) := by
      rw [← cancel_mono (V j).ι, Category.assoc, Scheme.homOfLE_ι, hl, e']
    change (G.obj.map gi.op).hom (s i) = (G.obj.map gj.op).hom (s j)
    rw [li, lj, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, LinearMap.comp_apply]
    exact congrArg (G.obj.map l.op).hom (hc i j))
  exact ⟨c, hc'⟩

theorem LeafZorn_of : LeafZorn := by
  intro R _ G X N hres hloc hfl W A V h a hcov hcomp
  let P : (Σ T : X.Opens, Sec G T.toScheme) → Prop :=
    fun p => ∀ k, rs inf_le_left p.2 - rs inf_le_right (a k) ∈ N (p.1 ⊓ V k)
  let r : {p // P p} → {p // P p} → Prop := fun p q => ∃ hh : p.1.1 ≤ q.1.1, rs hh q.1.2 = p.1.2
  have htrans : ∀ {p q s : {p // P p}}, r p q → r q s → r p s := by
    rintro p q s ⟨h1, e1⟩ ⟨h2, e2⟩
    exact ⟨h1.trans h2, by rw [← e1, ← e2, rs_rs]⟩
  have hchain : ∀ C : Set {p // P p}, IsChain r C → ∃ ub, ∀ p ∈ C, r p ub := by
    intro C hC
    let Vc : C → X.Opens := fun p => p.1.1.1
    obtain ⟨c, hc⟩ := glue G Vc (fun p : C => p.1.1.2) (by
      intro p q
      by_cases hpq : p.1 = q.1
      · obtain rfl : p = q := Subtype.ext hpq
        rfl
      · rcases hC p.2 q.2 hpq with ⟨hh, e⟩ | ⟨hh, e⟩
        · show rs inf_le_left p.1.1.2 = rs inf_le_right q.1.1.2
          rw [← e, rs_rs]
        · show rs inf_le_left p.1.1.2 = rs inf_le_right q.1.1.2
          rw [← e, rs_rs])
    refine ⟨⟨⟨⨆ p, Vc p, c⟩, fun k => ?_⟩, fun p hp => ⟨le_iSup Vc ⟨p, hp⟩, hc ⟨p, hp⟩⟩⟩
    apply hloc
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    change x ∈ (⨆ p, Vc p) at hx1
    rw [TopologicalSpace.Opens.mem_iSup] at hx1
    obtain ⟨p, hp⟩ := hx1
    have h' : Vc p ⊓ V k ≤ (⨆ p, Vc p) ⊓ V k := inf_le_inf_right _ (le_iSup Vc p)
    refine ⟨Vc p ⊓ V k, h', ⟨hp, hx2⟩, ?_⟩
    have key : rs h' (rs inf_le_left c - rs inf_le_right (a k)) =
        rs inf_le_left p.1.1.2 - rs inf_le_right (a k) := by
      rw [rs_sub, rs_rs, rs_rs, show rs (h'.trans inf_le_left) c = rs inf_le_left (rs (le_iSup Vc p) c) by
        rw [rs_rs], hc p]
    rw [key]
    exact p.1.2 k
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  have hVT : ∀ k, V k ≤ m.1.1 := by
    intro k
    have hd := m.2 k
    obtain ⟨n, hn, hnd⟩ := hfl _ _ inf_le_right _ hd
    let Vb : Bool → X.Opens := fun b => Bool.rec (V k) m.1.1 b
    have hn' := congrArg (rs (inf_comm (V k) m.1.1).le) hnd
    rw [rs_rs, rs_sub, rs_rs, rs_rs] at hn'
    obtain ⟨e, he⟩ := glue G Vb (fun b => Bool.rec (motive := fun b => Sec G (Vb b).toScheme) (a k + n) m.1.2 b) (by
      intro i j
      cases i <;> cases j
      · rfl
      · show rs inf_le_left (a k + n) = rs inf_le_right m.1.2
        rw [rs_add, hn']
        abel
      · show rs inf_le_left m.1.2 = rs inf_le_right (a k + n)
        rw [rs_add, hnd]
        abel
      · rfl)
    have hP : P ⟨⨆ b, Vb b, e⟩ := by
      intro l
      apply hloc
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      change x ∈ (⨆ b, Vb b) at hx1
      rw [TopologicalSpace.Opens.mem_iSup] at hx1
      obtain ⟨b, hb⟩ := hx1
      have h' : Vb b ⊓ V l ≤ (⨆ b, Vb b) ⊓ V l := inf_le_inf_right _ (le_iSup Vb b)
      refine ⟨Vb b ⊓ V l, h', ⟨hb, hx2⟩, ?_⟩
      have key : rs h' (rs inf_le_left e - rs inf_le_right (a l)) =
          rs inf_le_left (rs (le_iSup Vb b) e) - rs inf_le_right (a l) := by
        rw [rs_sub, rs_rs, rs_rs, rs_rs]
      rw [key, he b]
      cases b
      · show rs inf_le_left (a k + n) - rs inf_le_right (a l) ∈ N (V k ⊓ V l)
        rw [rs_add, show rs inf_le_left (a k) + rs inf_le_left n - rs inf_le_right (a l) =
          (rs inf_le_left (a k) - rs inf_le_right (a l)) + rs inf_le_left n by abel]
        exact add_mem (hcomp k l) (hres _ _ _ n hn)
      · exact m.2 l
    obtain ⟨hh, -⟩ := hm ⟨_, hP⟩ ⟨le_iSup Vb true, he true⟩
    exact (le_iSup Vb false).trans hh
  have hWT : W ≤ m.1.1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hcov x hx
    exact hVT k hk
  refine ⟨rs hWT m.1.2, fun k => ?_⟩
  have hk : V k ≤ m.1.1 ⊓ V k := le_inf (hVT k) le_rfl
  have key : rs hk (rs inf_le_left m.1.2 - rs inf_le_right (a k)) = rs (h k) (rs hWT m.1.2) - a k := by
    rw [rs_sub, rs_rs, rs_rs, rs_rs, rs_refl]
  rw [← key]
  exact hres _ _ hk _ (m.2 k)

end LateralTheory.CohomologicalPurity.ZornPf
end
end

