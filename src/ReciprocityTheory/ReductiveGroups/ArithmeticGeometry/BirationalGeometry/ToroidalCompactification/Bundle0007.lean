import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVDefect
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
variable {K : Type} [Fintype K] {Y Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}

theorem gm_gen_change {Z : Scheme.{0}} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (hp : ∀ k, φ k (r z) ∈ L.U (p k)) (hp' : ∀ k, φ k (r z) ∈ L.U (p' k)) :
    gm r z (LB.wchart L φ p) (t.s p) =
      (∏ k, gm (r ≫ φ k) z (L.U (p k) ⊓ L.U (p' k)) (L.g (p k) (p' k)) ^ ε k) * gm r z (LB.wchart L φ p') (t.s p') := by
  have m : r z ∈ (LB.LinComb L φ ε).U p ⊓ (LB.LinComb L φ ε).U p' :=
    ⟨Set.mem_iInter.2 fun k => hp k, Set.mem_iInter.2 fun k => hp' k⟩
  have e := congrArg (gm r z _) (ht p p')
  rw [gm_res r z _ m, map_mul, gm_res r z _ m] at e
  refine e.trans ?_
  congr 1
  show gm r z _ (∏ k, (res _ (pullU (φ k) _ (L.g (p k) (p' k)))) ^ ε k) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) ((gm_res r z _ m _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (p' k)) ⟨hp k, hp' k⟩ _))

theorem exists_defect (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ k, F (φ' k (r z)) ∈ L.U (p k)) → (∀ k, φ' k (r z) ∈ L'.U (q k)) →
      gm (r ≫ h) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ u * ((∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  classical
  have pt : ∀ k y, F (φ' k y) = φ k (h y) := fun k y => congrArg (fun g => g y) (hc k)
  let O : (K → L.ι) × (K → L'.ι) → Y'.Opens := fun pq => h ⁻¹ᵁ (LB.wchart L φ pq.1) ⊓ LB.wchart L' φ' pq.2
  have memO : ∀ pq x, x ∈ O pq ↔ (∀ k, φ k (h x) ∈ L.U (pq.1 k)) ∧ (∀ k, φ' k x ∈ L'.U (pq.2 k)) := fun pq x =>
    ⟨fun hx => ⟨fun k => Set.mem_iInter.1 hx.1 k, fun k => Set.mem_iInter.1 hx.2 k⟩,
      fun hx => ⟨Set.mem_iInter.2 hx.1, Set.mem_iInter.2 hx.2⟩⟩
  have l1 : ∀ pq k, O pq ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => pq.1 k) ⊓ L'.U (pq.2 k)) := fun pq k x hx =>
    ⟨Set.mem_iInter.2 fun _ => show F (φ' k x) ∈ L.U (pq.1 k) by rw [pt k x]; exact ((memO pq x).1 hx).1 k,
      ((memO pq x).1 hx).2 k⟩
  have l2 : ∀ pq, O pq ≤ h ⁻¹ᵁ (LB.wchart L φ pq.1) := fun _ => inf_le_left
  have l3 : ∀ pq, O pq ≤ LB.wchart L' φ' pq.2 := fun _ => inf_le_right
  let v : ∀ pq, Γ(Y', O pq)ˣ := fun pq =>
    res (l2 pq) (pullU h _ (t.s pq.1)) *
      ((∏ k, (res (l1 pq k) (pullU (φ' k) _ (w.s (fun _ => pq.1 k, pq.2 k)))) ^ ε k) * res (l3 pq) (a.s pq.2))⁻¹
  have gv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (pq : (K → L.ι) × (K → L'.ι)), r z ∈ O pq →
      gm r z (O pq) (v pq) = gm (r ≫ h) z (LB.wchart L φ pq.1) (t.s pq.1) *
        ((∏ k, gw w (r ≫ φ' k) z (pq.1 k) (pq.2 k) ^ ε k) * gm r z (LB.wchart L' φ' pq.2) (a.s pq.2))⁻¹ := by
    intro Z r z pq hz
    show gm r z (O pq) (res _ _ * ((∏ k, (res _ _) ^ ε k) * res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r h z _ (l2 pq hz) _)) ?_)
    refine (map_inv _ _).trans (congrArg (·⁻¹) ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hz _))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans (gm_pull r (φ' k) z _ (l1 pq k hz) _)))
  obtain ⟨s, hs⟩ := glue_unit ⊤ O (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hL (φ k (h x))
      choose q hq using fun k => exists_chart hL' (φ' k x)
      exact Opens.mem_iSup.2 ⟨(p, q), (memO (p, q) x).2 ⟨hp, hq⟩⟩) v (fun pq pq' x hx => by
      rw [gv Y' (𝟙 Y') x pq hx.1, gv Y' (𝟙 Y') x pq' hx.2]
      have m := (memO pq x).1 hx.1
      have m' := (memO pq' x).1 hx.2
      rw [gm_gen_change hL t ht (𝟙 Y' ≫ h) x pq.1 pq'.1 m.1 m'.1,
        gm_gen_change hL' a ha (𝟙 Y') x pq.2 pq'.2 m.2 m'.2]
      have hW : ∀ k, gw w (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq.2 k) =
          gm ((𝟙 Y' ≫ h) ≫ φ k) x _ (L.g (pq.1 k) (pq'.1 k)) *
            (gm (𝟙 Y' ≫ φ' k) x _ (L'.g (pq.2 k) (pq'.2 k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) x (pq'.1 k) (pq'.2 k) := by
        intro k
        have e := hw Y' (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq'.1 k) (pq.2 k) (pq'.2 k)
          (by show F (φ' k x) ∈ _; rw [pt]; exact m.1 k) (by show F (φ' k x) ∈ _; rw [pt]; exact m'.1 k)
          (m.2 k) (m'.2 k)
        rw [e, Category.assoc, Category.assoc, hc k]
      simp only [hW]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, inv_zpow', Finset.sum_add_distrib,
        smul_add, smul_neg, Finset.sum_neg_distrib, smul_eq_mul, neg_one_mul, neg_smul]
      abel)
  refine ⟨s, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ O (p, q) := (memO (p, q) (r z)).2 ⟨fun k => by rw [← pt]; exact hp k, hq⟩
  have e := gv Z r z (p, q) hz
  rw [← hs (p, q), gm_res r z _ hz] at e
  rw [e, inv_mul_cancel_right]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open ReciprocityTheory.ChartRestriction.G.Out

theorem globalFnsDvr_of_globalFns (hGF : GlobalFnsSt) : GlobalFnsDvrSt := by
  intro E _ _ _ H V _ _ _ _hcomp t hprop n
  letI : GrpObj t.G := t.grp
  have hsemi : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hsemi.smooth
  haveI : IsSeparated t.G.hom := hsemi.separated
  haveI : QuasiCompact t.G.hom := hsemi.quasiCompact
  obtain ⟨h1, h2, h3⟩ := GlobalFunctionsDvrGeneric.powObj_props t.G n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := hprop
  have hK := GlobalFunctionsDvrPowers.pull_powObj_globalFns hGF
    (spMap (algebraMap V (FractionRing V))) t.G hsemi n
  exact GlobalFunctionsDvrGeneric.bij_of_generic (powObj t.G n) hK

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem val_exists {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s]
    (y : Sp (FractionRing R) ⟶ X) (r : Sp R ⟶ S) (h : y ≫ s = Out.jK R ≫ r) :
    ∃ x : Sp R ⟶ X, Out.jK R ≫ x = y ∧ x ≫ s = r := by
  obtain ⟨hE, -⟩ : ValuativeCriterion.Existence s ∧ QuasiCompact s := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact this
  obtain ⟨⟨l⟩⟩ := hE ⟨R, FractionRing R, y, r, ⟨h⟩⟩
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem val_unique {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s]
    (x x' : Sp R ⟶ X) (h : Out.jK R ≫ x = Out.jK R ≫ x') (h' : x ≫ s = x' ≫ s) : x = x' := by
  obtain ⟨hU, -⟩ : ValuativeCriterion.Uniqueness s ∧ QuasiSeparated s := by
    have : (ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated) s := by
      rw [← IsSeparated.eq_valuativeCriterion]; infer_instance
    exact this
  have hsq : CommSq (Out.jK R ≫ x) (Out.jK R) s (x ≫ s) := ⟨Category.assoc _ _ _⟩
  have hs := hU ⟨R, FractionRing R, Out.jK R ≫ x, x ≫ s, hsq⟩
  exact congrArg CommSq.LiftStruct.l (@Subsingleton.elim _ hs ⟨x, rfl, rfl⟩ ⟨x', h.symm, h'.symm⟩)

theorem abLocus_pullback (hA : AbLocusOneSt) {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by
  have key : ∀ (K : Type) [Field K] (t : Sp K ⟶ S'),
      IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f)) := by
    intro K _ t
    have hp := (IsPullback.of_hasPullback G'.hom t).paste_horiz h
    have e : pullback.snd G'.hom t = hp.isoPullback.hom ≫ pullback.snd G.hom (t ≫ f) :=
      hp.isoPullback_hom_snd.symm
    rw [e]
    constructor
    · intro hpr
      rw [← Iso.inv_hom_id_assoc hp.isoPullback (pullback.snd G.hom (t ≫ f))]
      infer_instance
    · intro hpr
      infer_instance
  constructor
  · intro hfx
    have hfx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), f x ∈ Set.range t →
        IsProper (pullback.snd G.hom t) := hfx
    intro K _ _ t hxt
    obtain ⟨p, hp⟩ := hxt
    exact (key K t).2 (hfx' K (t ≫ f) ⟨p, congrArg (fun y => f y) hp⟩)
  · intro hx
    have hx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S'), x ∈ Set.range t →
        IsProper (pullback.snd G'.hom t) := hx
    let κ := AlgebraicClosure (S'.residueField x)
    let t : Sp κ ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ)) ≫
      S'.fromSpecResidueField x
    have hxt : x ∈ Set.range t := by
      have hr := Scheme.range_fromSpecResidueField (X := S') x
      refine ⟨IsLocalRing.closedPoint κ, ?_⟩
      have hm : (S'.fromSpecResidueField x).base
          ((Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ))).base
            (IsLocalRing.closedPoint κ)) ∈ ({x} : Set S') := hr ▸ ⟨_, rfl⟩
      exact hm
    have hp := (key κ t).1 (hx' κ t hxt)
    obtain ⟨p, hp'⟩ := hxt
    exact hA S G hG κ (t ≫ f) hp ⟨p, congrArg (fun y => f y) hp'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem Model.j_s {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem dom_iff {O₀ O : Type} [CommRing O₀] [CommRing O] {β₀ : O₀ →+* c.F} {β : O →+* c.F} {b : O₀ →+* O}
    {Yg : Model Xo c β₀} {Y : Model Xo c β} {f : pullback Yg.s (spMap b) ⟶ Y.X} {t₁ : SAB H (pullback Yg.s (spMap b))}
    (m₁ : SABMap t₁ Yg.t (pullback.fst _ _)) (m₂ : SABMap t₁ Y.t f)
    (hc : ∀ (T : Scheme.{0}) (g : T ⟶ t₁.G.left) (g₁ : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Yg.m.φ → g₁ ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
      g₁ ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y.m.φ)
    (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)) (haF : aF ≫ pullback.fst _ _ = Yg.j) {T : Scheme.{0}}
    (g : T ⟶ t₁.G.left) (gg : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left)
    (h₀ : gg ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ) (h₁ : gg ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom)
    (hb : g ≫ t₁.G.hom = gg ≫ Yg.oF.t.G.hom ≫ aF) : g ≫ m₁.φ = gg ≫ Yg.m.φ ↔ g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  refine ⟨fun h => hc T g gg g₂ h h₀ h₁, fun h2 => ?_⟩
  have w1 : (gg ≫ Yg.m.φ) ≫ Yg.t.G.hom = (g ≫ t₁.G.hom) ≫ pullback.fst Yg.s (spMap b) := by
    have e1 := Yg.m.cart.1.w
    have e2 : aF ≫ pullback.fst Yg.s (spMap b) = Yg.jQ ≫ pullback.fst _ _ := haF
    simp only [SABMap.φ, Category.assoc] at e1 ⊢
    rw [e1, reassoc_of% hb, e2]
  let k := m₁.cart.1.lift (gg ≫ Yg.m.φ) (g ≫ t₁.G.hom) w1
  have hk1 : k ≫ m₁.φ = gg ≫ Yg.m.φ := m₁.cart.1.lift_fst _ _ _
  have hk2 : k ≫ t₁.G.hom = g ≫ t₁.G.hom := m₁.cart.1.lift_snd _ _ _
  have hk3 : k ≫ m₂.φ = g₂ ≫ Y.m.φ := hc T k gg g₂ hk1 h₀ h₁
  have hkg : k = g := m₂.cart.1.hom_ext (by rw [hk3, h2]) hk2
  rw [← hkg]
  exact hk1

theorem oneArc (hC : SABCompSt) (hX : SABCancelSt) (hA : AbLocusOneSt) (hP : ProjProperSt) : OneArcSt := by
  intro E _ _ _ H D l Xo c k _ bF a O₀ O O' _ _ _ β₀ β β' b b' Yg Y Y' hb hb' hmono hD hD' χ W y hχ hy hys
  obtain ⟨f, t₁, m₁, m₂, hf, hj, hc⟩ := hD
  obtain ⟨f', t₁', m₁', m₂', hf', hj', hc'⟩ := hD'
  have := hP _ _ _ Yg.proj
  have := hP _ _ _ Y.proj
  have e₀ : spMap β₀ = spMap β ≫ spMap b := by rw [← hb, spMap_comp]
  have e₀' : spMap β₀ = spMap β' ≫ spMap b' := by rw [← hb', spMap_comp]
  obtain ⟨χg, hg₁, hg₂⟩ := val_exists Yg.s (y ≫ Yg.j) (spMap (PowerSeries.C (R := k)) ≫ spMap bF ≫ spMap β₀)
    (by rw [Category.assoc, Yg.j_s, ← Category.assoc, hys]; simp only [Category.assoc])
  have mk : ∀ {O : Type} [CommRing O] (β : O →+* c.F) (b : O₀ →+* O), spMap β₀ = spMap β ≫ spMap b →
      ∃ (χ₁ : Sp (PowerSeries k) ⟶ pullback Yg.s (spMap b)) (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)),
        χ₁ ≫ pullback.fst _ _ = χg ∧ χ₁ ≫ pullback.snd _ _ = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β) ∧
        aF ≫ pullback.fst _ _ = Yg.j ∧ Out.jK (PowerSeries k) ≫ χ₁ = y ≫ aF := by
    intro O _ β b e
    refine ⟨pullback.lift χg (spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β))
        (by rw [hg₂, e, spMap_comp]; simp only [Category.assoc]),
      pullback.lift Yg.j (pullback.snd _ _ ≫ spMap β) (by rw [Yg.j_s, e, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, hg₁]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc y, hys, spMap_comp]
      simp only [Category.assoc]
  obtain ⟨χ₁, aF, h1, h2, h3, h4⟩ := mk β b e₀
  obtain ⟨χ₁', aF', h1', h2', h3', h4'⟩ := mk β' b' e₀'
  have hχ₁ : χ = χ₁ ≫ f := val_unique Y.s _ _
    (by rw [← hy, ← Category.assoc, h4, Category.assoc, hj aF h3]) (by rw [hχ, Category.assoc, hf, h2])
  subst hχ₁
  obtain ⟨n₁, hn₁⟩ := hX E H _ _ _ _ _ _ _ _ m₂ W.m
  obtain ⟨ng, hng⟩ := hC E H _ _ _ _ _ _ _ _ m₁ n₁
  have cancel : ∀ (p : Sp (PowerSeries k) ⟶ Yg.X) (_ : p = χ₁' ≫ pullback.fst _ _) (n : SABMap W.t Yg.t p),
      ∃ m' : SABMap W.t t₁' χ₁', n.φ = m'.φ ≫ m₁'.φ := by
    intro p hp n; subst hp; exact hX E H _ _ _ _ _ _ _ _ m₁' n
  obtain ⟨n₁', hn₁'⟩ := cancel _ (h1.trans h1'.symm) ng
  obtain ⟨m', hm'⟩ := hC E H _ _ _ _ _ _ _ _ m₂' n₁'
  have hy' : y ≫ Y'.j = Out.jK (PowerSeries k) ≫ χ₁' ≫ f' := by
    rw [← Category.assoc, h4', Category.assoc, hj' aF' h3']

  have tr : ∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left)
      (τ : T ⟶ Sp (FractionRing (PowerSeries k))), g ≫ W.t.G.hom = τ ≫ Out.jK (PowerSeries k) →
      g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
      g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → (g ≫ W.m.φ = g₁ ≫ Y.m.φ ↔ g ≫ m'.φ = g₂ ≫ Y'.m.φ) := by
    intro T g g₁ g₂ τ hg hg₁ k₀ k₁
    have w : (g₁ ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = (g₁ ≫ Y.oF.t.G.hom) ≫ pullback.fst _ _ := by
      rw [Category.assoc, Y.m0.toSABMap.cart.1.w, Category.assoc]
    have u₀ := Yg.m0.toSABMap.cart.1.lift_fst _ _ w
    have u₁ := Yg.m0.toSABMap.cart.1.lift_snd _ _ w
    have A := dom_iff m₁ m₂ hc aF h3 (g ≫ n₁.φ) _ g₁ u₀ u₁ (by
      rw [Category.assoc, n₁.cart.1.w, ← Category.assoc, hg, Category.assoc, h4, ← Category.assoc _ Yg.oF.t.G.hom aF, u₁,
        hg₁, Category.assoc])
    have B := dom_iff m₁' m₂' hc' aF' h3' (g ≫ n₁'.φ) _ g₂ (u₀.trans k₀) (u₁.trans k₁) (by
      rw [Category.assoc, n₁'.cart.1.w, ← Category.assoc, hg, Category.assoc, h4', ← Category.assoc _ Yg.oF.t.G.hom aF', u₁,
        hg₁, Category.assoc])
    rw [hn₁, hm', ← Category.assoc, ← Category.assoc, ← A, ← B, Category.assoc, Category.assoc, ← hng, ← hn₁']
  have : Mono Y'.j := by
    have := Y'.jQ_open
    have := hmono
    unfold Model.j; infer_instance
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  refine ⟨χ₁' ≫ f', ⟨W.t, m', W.P, W.φ, W.he, W.w, W.e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
    ⟨(s6 F uF ha hu).1, fun yF hyF n p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩, ?_, hy', fun x => ?_, rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, fun T g g' g₁ g₂ τ hgg hg hg₁ h k₀ k₁ => ?_⟩
  · have hyF' : yF = Out.jFK (R := PowerSeries k) F ≫ y := by
      rw [← cancel_mono Y'.j, hyF, Category.assoc, hy']
    have base : (x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK (PowerSeries k))) ≫ W.t.G.hom =
        Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k) := by
      have a₁ : W.P.U.gen.inv.left ≫ pullback.snd W.t.G.hom (Out.jK (PowerSeries k)) = W.P.A.A.hom :=
        Over.w W.P.U.gen.inv
      have a₂ : x.left ≫ W.P.A.A.hom = Out.jFK (R := PowerSeries k) F := Over.w x
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd _ _), a₁,
        ← Category.assoc, a₂]
    have go : ∀ (σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), σY.left ≫ Y.m0.toSABMap.φ = σ.left ≫ Y'.m0.toSABMap.φ →
        x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK (PowerSeries k)) ≫ W.m.φ =
          yF ≫ σY.left ≫ Y.m.φ := by
      intro σY hσY
      have b₁ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σY
      have b₂ : σ.left ≫ Y'.oF.t.G.hom = 𝟙 _ := Over.w σ
      have := (tr _ _ (yF ≫ σY.left) (yF ≫ σ.left) _ base (by rw [Category.assoc, b₁, hyF']; exact Category.comp_id _)
        (by rw [Category.assoc, hσY, Category.assoc]) (by rw [Category.assoc, b₁, Category.assoc, b₂])).2
        (by simpa only [Category.assoc] using e4)
      simpa only [Category.assoc] using this
    have hyY : yF ≫ Y.j = Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k) ≫ χ₁ ≫ f := by
      rw [hyF', Category.assoc, hy]
    rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
    · exact (s6 F uF ha hu).2 yF hyY n p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Y.m0.etaA v).trans (Y'.m0.etaA v).symm))
    · exact (s6 F uF ha hu).2 yF hyY n p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Y.m0.eta v).trans (Y'.m0.eta v).symm))
  · rw [Category.assoc, hf', h2']
  · have q₁ := abLocus_pullback hA Y'.t.semi m'.cart.1 x
    have q₂ := abLocus_pullback hA Y.t.semi W.m.cart.1 x
    exact q₁.trans q₂.symm
  · have hgg' : (show T ⟶ W.t.G.left from g') = g := eq_of_heq hgg
    have q := (tr T g g₁ g₂ τ hg hg₁ k₀ k₁).1 h
    rw [← hgg'] at q
    exact q

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

