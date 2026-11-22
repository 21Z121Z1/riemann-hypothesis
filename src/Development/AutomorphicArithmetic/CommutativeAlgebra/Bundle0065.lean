import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsogenyWithKernelSubgroup
import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3668
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyKernelPointsIffOfIsPIsog
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsoOfPIsogenyKernelEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3664
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RepDataGeometricPointsOfSubData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

noncomputable section

namespace UpperTheory.SectionEquivalence

variable {T U : Scheme.{0}} {G' : Over T} [GrpObj G'] {G : Over U} [GrpObj G] {f : T ⟶ U} {φ : G'.left ⟶ G.left}

private theorem mul_left (hp : IsGrpPullback G' G f φ) (h h' : 𝟙_ (Over T) ⟶ G') {g : T ⟶ U} (hg : 𝟙 T ≫ f = g)
    (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = h.left ≫ φ) (hy : y₀.left = h'.left ≫ φ) :
    (x₀ * y₀).left = (h * h').left ≫ φ := by
  subst hg
  exact hp.2 _ h h' x₀ y₀ hx hy

private def secEquiv (hp : IsGrpPullback G' G f φ) : (𝟙_ (Over T) ⟶ G') ≃* (Over.mk f ⟶ G) where
  toFun h := Over.homMk (h.left ≫ φ) (by
    have e : h.left ≫ G'.hom = 𝟙 T := Over.w h
    show (h.left ≫ φ) ≫ G.hom = f
    rw [Category.assoc, hp.1.w, ← Category.assoc, e]
    exact Category.id_comp f)
  invFun a := (Over.homMk (hp.1.lift a.left (𝟙 T) ((Over.w a).trans (Category.id_comp f).symm))
    (hp.1.lift_snd _ _ _) : Over.mk (𝟙 T) ⟶ G')
  left_inv h := by
    have e : h.left ≫ G'.hom = 𝟙 T := Over.w h
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_)
    · exact hp.1.lift_fst _ _ _
    · exact (hp.1.lift_snd _ _ _).trans e.symm
  right_inv a := Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  map_mul' h h' := Over.OverMorphism.ext
    (mul_left hp h h' (Category.id_comp f) _ _ rfl rfl).symm

private theorem secEquiv_left (hp : IsGrpPullback G' G f φ) (h : 𝟙_ (Over T) ⟶ G') :
    (secEquiv hp h).left = h.left ≫ φ := rfl

private theorem secEquiv_comp {H' : Over T} [GrpObj H'] {H : Over U} [GrpObj H] {φ₁ : H'.left ⟶ H.left}
    (hp : IsGrpPullback G' G f φ) (hp₁ : IsGrpPullback H' H f φ₁) (α : G' ⟶ H') (β : G ⟶ H)
    (e : α.left ≫ φ₁ = φ ≫ β.left) (h : 𝟙_ (Over T) ⟶ G') :
    secEquiv hp₁ (h ≫ α) = secEquiv hp h ≫ β := by
  refine Over.OverMorphism.ext ?_
  rw [secEquiv_left, Over.comp_left, Over.comp_left, secEquiv_left, Category.assoc, Category.assoc, e]

end UpperTheory.SectionEquivalence

open UpperTheory.SectionEquivalence

theorem UpperTheory.repData_geometric_points_of_subData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ y : Sp k ⟶ Rd.Y.left, y ≫ Rd.Y.hom = x ∧ KerGeo Rd Sd y := by
  intro p _ D R _ _ b N hN hNp hpu hm r w j c hw hr hj hc S _ s o Rd Sd k _ _ x
  obtain ⟨ox, ⟨m⟩⟩ := IsogRep.exists_pull x o (s' := x ≫ s) rfl
  have hp' : IsGrpPullback ox.A o.A x m.φ := m.cart
  letI := Sd.grp
  haveI := Sd.hom
  let Ksub : Subgroup (Over.mk x ⟶ o.A) := (IsMonHom.monoidHom Sd.i (Over.mk x)).range
  let H₀ : Subgroup (𝟙_ (Over (Sp k)) ⟶ ox.A) := Ksub.comap (secEquiv hp').toMonoidHom
  have memH : ∀ h, h ∈ H₀ ↔ InSub Sd.i (secEquiv hp' h) := fun h => Iff.rfl
  have hstab : ∀ (a : D.O), ∀ h ∈ H₀, h ≫ ox.act.act a ∈ H₀ := by
    intro a h hh
    rw [memH] at hh ⊢
    obtain ⟨z, hz⟩ := hh
    obtain ⟨g, hg⟩ := Sd.stable a
    refine ⟨z ≫ g, ?_⟩
    rw [secEquiv_comp hp' hp' _ _ (m.act a) h, Category.assoc, hg, ← Category.assoc, hz]
  have hkill : ∀ h ∈ H₀, ES.KilledBy ox w h := by
    intro h hh c hc
    have hk := Sd.killed _ _ ((memH h).1 hh) c hc
    rw [← secEquiv_comp hp' hp' _ _ (m.act _) h, ← map_one (secEquiv hp')] at hk
    exact (secEquiv hp').injective hk
  have hcard : Nat.card H₀ = Ideal.absNorm w ^ j := by
    haveI := Sd.mono
    haveI := Sd.fin
    haveI := Sd.et
    have hmem : ∀ z : Over.mk x ⟶ Sd.K, (secEquiv hp').symm (z ≫ Sd.i) ∈ H₀ := fun z => by
      rw [memH, MulEquiv.apply_symm_apply]
      exact ⟨z, rfl⟩
    have e1 : H₀ ≃ (Over.mk x ⟶ Sd.K) := by
      refine (Equiv.ofBijective (fun z : Over.mk x ⟶ Sd.K => (⟨_, hmem z⟩ : H₀)) ⟨?_, ?_⟩).symm
      · intro z z' hzz
        have hz := congrArg (fun u : H₀ => secEquiv hp' u.1) hzz
        simp only [MulEquiv.apply_symm_apply] at hz
        exact (cancel_mono Sd.i).1 hz
      · rintro ⟨h, hh⟩
        obtain ⟨z, hz⟩ := (memH h).1 hh
        refine ⟨z, Subtype.ext ?_⟩
        simp only [hz, MulEquiv.symm_apply_apply]
    have e2 : (Over.mk x ⟶ Sd.K) ≃ {t : Spec (CommRingCat.of k) ⟶ Sd.K.left // t ≫ Sd.K.hom = x} :=
      { toFun := fun z => ⟨z.left, by simpa using Over.w z⟩
        invFun := fun t => Over.homMk t.1 t.2
        left_inv := fun z => Over.OverMorphism.ext rfl
        right_inv := fun t => Subtype.ext rfl }
    let pt : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank Sd.K.hom x pt
    rw [Nat.card_congr (e1.trans e2), hc]
    have hK : (toUnit Sd.K).left = Sd.K.hom := by simpa using Over.w (toUnit Sd.K)
    have hr := Sd.deg.rank (x pt)
    rw [hK] at hr
    exact hr
  obtain ⟨o', ψ, hiso, htj, hker⟩ :=
    UpperTheory.exists_isogeny_with_kernel_subgroup p D R b N hN hNp hpu hm r w j c hw hr hc k (x ≫ s) ox H₀ hstab hkill hcard
  obtain ⟨y, ⟨hy, m₀', m₁, hsq⟩, -⟩ := Rd.univ (Sp k) x ox o' m ψ hiso htj
  subst hy
  refine ⟨y, rfl, ?_⟩
  intro a₀ a ha
  have hp₀ := m₀'.cart
  have hp₁ := m₁.cart
  obtain ⟨mm, hmm⟩ := IsogRep.exists_comp m₀' Rd.m₀
  have hφ : m.φ = m₀'.φ ≫ Rd.m₀.φ := by
    rw [← hmm]
    exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ o ox _ _ m mm rfl
  obtain ⟨h, rfl⟩ : ∃ h, secEquiv hp₀ h = a₀ := ⟨(secEquiv hp₀).symm a₀, MulEquiv.apply_symm_apply _ _⟩
  have haa : a = secEquiv hp' h := by
    apply Over.OverMorphism.ext
    rw [secEquiv_left, hφ, ← Category.assoc, ← secEquiv_left hp₀, ha]
  have hψ1 : secEquiv hp₀ h ≫ Rd.ψ = secEquiv hp₁ (h ≫ ψ) :=
    (secEquiv_comp hp₀ hp₁ ψ Rd.ψ hsq.symm h).symm
  have hkb : ∀ I : Ideal (𝓞 D.F), ES.KilledBy Rd.o₀ I (secEquiv hp₀ h) ↔ ES.KilledBy ox I h := by
    intro I
    refine forall₂_congr fun c _ => ?_
    rw [← secEquiv_comp hp₀ hp₀ _ _ (m₀'.act _) h, ← map_one (secEquiv hp₀),
      (secEquiv hp₀).injective.eq_iff]
  rw [haa, ← memH, ← hker, hψ1, ← map_one (secEquiv hp₁), (secEquiv hp₁).injective.eq_iff]
  simp only [hkb]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SubDataPointsCorrespondRepData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.KernelTorsionPullback

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem exists_equiv_points_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  let Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G) :=
    { toFun := fun x => Over.homMk (x.left ≫ φ) (by
        show _ = T.hom ≫ f
        rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
      invFun := fun y => Over.homMk (hp.1.lift y.left T.hom (Over.w y)) (by simp)
      left_inv := fun x => by
        apply Over.OverMorphism.ext
        apply hp.1.hom_ext
        · simp
        · simp
      right_inv := fun y => by
        apply Over.OverMorphism.ext
        simp }
  have hl : ∀ x, (Φ x).left = x.left ≫ φ := fun x => rfl
  have h1 : Φ 1 = 1 := by
    have hm := hp.2 T 1 1 (Φ 1) (Φ 1) (hl 1) (hl 1)
    have hsq : Φ 1 * Φ 1 = Φ 1 := by
      apply Over.OverMorphism.ext
      rw [hm, _root_.mul_one]
      rfl
    exact mul_left_cancel (a := Φ 1) (by rw [hsq, _root_.mul_one])
  refine ⟨Φ, hl, fun x => ⟨fun hx => Φ.injective (by rw [hx, h1]), fun hx => by rw [hx, h1]⟩⟩

private theorem isTj_of_pull {Y S : Scheme.{0}} {σ : Y ⟶ Sp R} {σ₁ : S ⟶ Sp R} {f : S ⟶ Y} {r : ℤ}
    {w : Ideal (𝓞 D.F)} {j : ℕ} {o o' : Obj b N σ} {o₁ o₁' : Obj b N σ₁}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) {ψ : o.A ⟶ o'.A} {ψ₁ : o₁.A ⟶ o₁'.A}
    (e : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (h : IsTj r w j o o' ψ) : IsTj r w j o₁ o₁' ψ₁ := by
  intro k _ _ _ x
  obtain ⟨h1, h2⟩ := h k (x ≫ f)
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_of_isGrpPullback m.cart (Over.mk x)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_of_isGrpPullback m'.cart (Over.mk x)
  have hψ : ∀ g, Φ' (g ≫ ψ₁) = Φ g ≫ ψ := by
    intro g
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, e]
  have hk1 : ∀ g, g ≫ ψ₁ = 1 ↔ Φ g ≫ ψ = 1 := by
    intro g
    rw [← hψ, hΦ'1]
  have hkill : ∀ v g, KilledBy o₁ v g ↔ KilledBy o v (Φ g) := by
    intro v g
    apply forall₂_congr
    intro a _
    have hc : Φ (g ≫ o₁.act.act ((algebraMap (𝓞 D.F) D.O) a))
        = Φ g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) a) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, m.act]
    rw [← hc, hΦ1]
  constructor
  · intro g hg hex
    rw [hkill]
    obtain ⟨e0, he⟩ := hex
    exact h1 (Φ g) ((hk1 g).mp hg) ⟨e0, (hkill _ g).mp he⟩
  · rw [← h2]
    exact Nat.card_congr (Φ.subtypeEquiv (fun g => by rw [hk1, hkill]))

private theorem exists_equiv_points_mk_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk g ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  subst hg
  exact exists_equiv_points_of_isGrpPullback hp T

private theorem ker_iff {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s}
    (Rd : RepData b N r w j c s o) (Sd : SubData w j o) {k : Type} [Field k] (y : Sp k ⟶ Rd.Y.left) {x : Sp k ⟶ S}
    (e : y ≫ Rd.Y.hom = x) {t : Sp k ⟶ Sp R} {ox o₁ : Obj b N t} (m : ObjMap ox o x) (my : ObjMap ox Rd.o₀ y)
    (hm : my.φ ≫ Rd.m₀.φ = m.φ) (n : ObjMap o₁ Rd.o' y) (ψ₁ : ox.A ⟶ o₁.A)
    (hψ : my.φ ≫ Rd.ψ.left = ψ₁.left ≫ n.φ) (hK : KerGeo Rd Sd y) (h : Over.mk (𝟙 (Sp k)) ⟶ ox.A)
    (a : Over.mk x ⟶ o.A) (ha : a.left = h.left ≫ m.φ) :
    (h ≫ ψ₁ = 1 ∧ ∃ e : ℕ, KilledBy ox (uIdeal D r ^ e) h) ↔ InSub Sd.i a := by
  subst e
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_mk_of_isGrpPullback my.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_mk_of_isGrpPullback n.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  have key := hK (Φ h) a (by rw [hΦl, Category.assoc, hm, ha])
  rw [← key]
  have hψ' : Φ' (h ≫ ψ₁) = Φ h ≫ Rd.ψ := by
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, hψ]
  have hk : ∀ v, KilledBy ox v h ↔ KilledBy Rd.o₀ v (Φ h) := by
    intro v
    apply forall₂_congr
    intro c _
    have hc : Φ (h ≫ ox.act.act ((algebraMap (𝓞 D.F) D.O) c))
        = Φ h ≫ Rd.o₀.act.act ((algebraMap (𝓞 D.F) D.O) c) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, my.act]
    rw [← hc, hΦ1]
  rw [← hψ', hΦ'1]
  exact and_congr Iff.rfl (exists_congr fun _ => hk _)

end UpperTheory.KernelTorsionPullback

private theorem exists_objMap_same_phi_of_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f f' : S' ⟶ S}
    (hf : f = f') (n : ObjMap o' o f) : ∃ n' : ObjMap o' o f', n'.φ = n.φ := by
  subst hf
  exact ⟨n, rfl⟩

open UpperTheory.KernelTorsionPullback in
theorem UpperTheory.subData_points_correspond_repData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o) (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Rd.Y.left), y₁ ≫ Rd.Y.hom = y₂ ≫ Rd.Y.hom → KerGeo Rd Sd y₁ → KerGeo Rd Sd y₂ → y₁ = y₂ := by
  intro p _ D R _ _ b N hN hcop hp hm1 r w j c hw hu hc S _ s o Rd Sd k _ _ y₁ y₂ hy hK₁ hK₂
  obtain ⟨x, hx⟩ : ∃ x, y₁ ≫ Rd.Y.hom = x := ⟨_, rfl⟩
  have hx2 : y₂ ≫ Rd.Y.hom = x := hy ▸ hx
  obtain ⟨ox, ⟨my₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o₀ (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨o₁, ⟨n₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o' (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨ψ₁, hiso₁, hsq₁⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₁ Rd.o₀ Rd.o' ox o₁ my₁ n₁ Rd.ψ Rd.isog
  have htj₁ : IsTj r w j ox o₁ ψ₁ := isTj_of_pull my₁ n₁ hsq₁ Rd.tj
  obtain ⟨mc, hmc⟩ := IsogRep.exists_comp my₁ Rd.m₀
  obtain ⟨m, hmφ⟩ := exists_objMap_same_phi_of_eq hx mc
  obtain ⟨my₂, hmy₂⟩ := IsogRep.exists_factor hN hcop hx2 Rd.m₀ m
  obtain ⟨o₂, ⟨n'⟩⟩ := IsogRep.exists_pull y₂ Rd.o' (s' := x ≫ s) (by rw [← hx2, Category.assoc])
  obtain ⟨ψ₂, hiso₂, hsq₂⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₂ Rd.o₀ Rd.o' ox o₂ my₂ n' Rd.ψ Rd.isog
  have hker : ∀ h : 𝟙_ (Over (Sp k)) ⟶ ox.A,
      (h ≫ ψ₁ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) ↔
        (h ≫ ψ₂ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) := by
    intro h
    let a : Over.mk x ⟶ o.A := Over.homMk (h.left ≫ m.φ) (by
      show _ = x
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w h]
      exact Category.id_comp x)
    rw [ker_iff Rd Sd y₁ hx m my₁ (by rw [hmφ, hmc]) n₁ ψ₁ hsq₁ hK₁ h a rfl,
      ker_iff Rd Sd y₂ hx2 m my₂ hmy₂ n' ψ₂ hsq₂ hK₂ h a rfl]
  have hgeo := isogeny_kernel_points_iff_of_isPIsog p D R b N hp r w c hw hu k (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hker
  obtain ⟨mm, hmm⟩ := exists_iso_of_pIsogeny_kernel_eq p D R b N hN hcop hp c (Sp k) (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hgeo
  obtain ⟨nc, hnc⟩ := IsogRep.exists_comp mm n'
  obtain ⟨n₂, hn₂⟩ := exists_objMap_same_phi_of_eq (Category.id_comp y₂) nc
  exact (Rd.univ (Sp k) x ox o₁ m ψ₁ hiso₁ htj₁).unique ⟨hx, my₁, n₁, hsq₁⟩
    ⟨hx2, my₂, n₂, by rw [hn₂, hnc, ← Category.assoc, hmm, hsq₂]⟩
end

