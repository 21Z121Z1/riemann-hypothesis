import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
import Development.EtaleCohomology.EtaleSheaves.Bundle0044
import Development.EtaleCohomology.EtaleSheaves.Bundle0047
import Development.EtaleCohomology.EtaleSheaves.Bundle0045

-- bundled from Development.EtaleCohomology.EtaleSheaves.PushColim
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

abbrev PP (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) := pull (ZMod q) (sch.map (Spec.map f)) (tw q i) n
theorem PP_comp (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (x) :
    PP q i n (f ≫ g) x = PP q i n g (PP q i n f x) := by
  rw [PP, Spec.map_comp, Functor.map_comp, pull_comp]
theorem unit_of {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) : IsUnit (q : B) := by
  simpa using h.map f.hom

abbrev HR (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) := Hrel (ZMod q) (sch.map (Spec.map φ)) (tw q i) n

abbrev RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) : HR q i n φ →+ HR q i n ψ :=
  rpl q i (Spec.map φ) (Spec.map ψ) (Spec.map u) (Spec.map e) (by rw [← Spec.map_comp, ← Spec.map_comp, h]) n

theorem RP_comp (q : ℕ) (i n : ℤ) {D Y E Z E' Z' : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) (e' : E ⟶ E') (u' : Z ⟶ Z') (ψ' : E' ⟶ Z') (h' : ψ ≫ u' = e' ≫ ψ') (e2 : D ⟶ E') (u2 : Y ⟶ Z')
    (h2 : φ ≫ u2 = e2 ≫ ψ') (he : e ≫ e' = e2) (hu : u ≫ u' = u2) (z : HR q i n φ) :
    RP q i n φ e2 u2 ψ' h2 z = RP q i n ψ e' u' ψ' h' (RP q i n φ e u ψ h z) :=
  rpull_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [← hu, Spec.map_comp, Functor.map_comp])
    (by rw [← he, Spec.map_comp, Functor.map_comp]) n z

theorem RP_bd (q : ℕ) (i m n : ℤ) (hm : 1 + m = n) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (y) :
    RP q i n φ e u ψ h (bd _ _ _ m n hm y) = bd _ _ _ m n hm (PP q i m u y) := rpull_bd ..

theorem fgt_RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (z : HR q i n φ) :
    fgt _ _ _ n (RP q i n φ e u ψ h z) = PP q i n e (fgt _ _ _ n z) := relNat _ _ _ _ _ _ _ n z

theorem pushColim {A Y C Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y') (φ' : C ⟶ Y')
    (hpo : IsPushout φ c w φ') {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (s : D ⟶ (Functor.const J).obj C) (hc : IsColimit (Cocone.mk _ s))
    (ht : ∀ j, t.app j ≫ s.app j = c) :
    ∃ (E : J ⥤ CommRingCat.{0}) (p : D ⟶ E) (e : E ⟶ (Functor.const J).obj Y') (v : ∀ j, Y ⟶ E.obj j),
      Nonempty (IsColimit (Cocone.mk _ e)) ∧ (∀ j, IsPushout φ (t.app j) (v j) (p.app j)) ∧
      (∀ j, p.app j ≫ e.app j = s.app j ≫ φ') ∧ ∀ j k (f : j ⟶ k), v j ≫ E.map f = v k := by
  have : IsConnected J := IsFiltered.isConnected J
  let F : J ⥤ Under A := D.toUnder A (fun j => t.app j) (fun {j k} g => by
    have := t.naturality g
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    exact this.symm)
  let cU : Cocone F :=
    { pt := Under.mk c
      ι := { app := fun j => Under.homMk (s.app j) (ht j)
             naturality := fun j k g => by
               apply Under.UnderMorphism.ext
               exact s.naturality g } }
  have hcU : IsColimit cU := isColimitOfReflects (Under.forget A) (by exact hc)
  have h2 := isColimitOfPreserves (Under.pushout φ ⋙ Under.forget Y) hcU
  let E : J ⥤ CommRingCat.{0} := F ⋙ Under.pushout φ ⋙ Under.forget Y
  let e : E ⟶ (Functor.const J).obj Y' :=
    ((Under.pushout φ ⋙ Under.forget Y).mapCocone cU).ι ≫ (Functor.const J).map hpo.flip.isoPushout.inv
  have hE : IsColimit (Cocone.mk _ e) :=
    h2.ofIsoColimit (Cocone.ext hpo.flip.isoPushout.symm (fun j => rfl))
  let p : D ⟶ E :=
    { app := fun j => (pushout.inl (t.app j) φ : D.obj j ⟶ pushout (t.app j) φ)
      naturality := fun j k g => by
        exact (pushout.inl_desc _ _ _).symm }
  refine ⟨E, p, e, fun j => pushout.inr (t.app j) φ, ⟨hE⟩, fun j => (IsPushout.of_hasPushout (t.app j) φ).flip,
    fun j => ?_, fun j k f => pushout.inr_desc _ _ _⟩
  have key : ∀ h, pushout.inl (t.app j) φ ≫ (pushout.desc (s.app j ≫ pushout.inl c φ) (pushout.inr c φ) h ≫
      hpo.flip.isoPushout.inv) = s.app j ≫ φ' := by
    intro h; rw [← Category.assoc, pushout.inl_desc, Category.assoc, hpo.flip.inl_isoPushout_inv]
  exact key _

theorem relAt (hB1 : B1) (q : ℕ) (i n : ℤ) {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (hq : IsUnit (q : D)) (o : D ⟶ O)
    (hIE : IE o) (hBC : BC q i φ' o) (z : HR q i n φ') (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (s : E ⟶ O) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z)
      (h : IsPushout φ' e u ψ), Et e ∧ e ≫ s = o ∧ RP q i n φ' e u ψ h.w z = 0 := by
  obtain ⟨J, _, _, F, t, s, hc, hts⟩ := hIE
  have hZ := IsPushout.of_hasPushout φ' o
  set ψ := pushout.inr φ' o
  have hRE := hBC _ _ _ hZ
  obtain ⟨G, p, e, v, ⟨hG⟩, hpo, hpe, hv⟩ := pushColim φ' o _ ψ hZ F t s hc (fun j => (hts j).2)
  have hnat : ∀ {j k} (f : j ⟶ k), t.app j ≫ F.map f = t.app k := fun f => by simpa using (t.naturality f).symm
  have hs : ∀ {j k} (f : j ⟶ k), F.map f ≫ s.app k = s.app j := fun f => by simpa using s.naturality f
  have he : ∀ {j k} (f : j ⟶ k), G.map f ≫ e.app k = e.app j := fun f => by simpa using e.naturality f
  have hxO : PP q i n o (fgt _ _ _ n z) = 0 := by
    apply (hRE n).1
    change PP q i n ψ _ = _
    rw [map_zero, ← PP_comp, ← hZ.w, PP_comp, hz, map_zero]
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨k, f, hk⟩ := (hB1 q F _ hc n i).2 j0 (PP q i n (t.app j0) (fgt _ _ _ n z)) (unit_of (t.app j0) hq) (by
    change PP q i n (s.app j0) _ = 0
    rw [← PP_comp, (hts j0).2, hxO])
  change PP q i n (F.map f) _ = 0 at hk
  rw [← PP_comp, hnat] at hk
  have hm : 1 + (n - 1) = n := by omega
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm (RP q i n φ' (t.app k) (v k) (p.app k) (hpo k).w z)
    (by rw [fgt_RP]; exact hk)
  obtain ⟨a, ha⟩ := (hRE (n - 1)).2 (PP q i (n - 1) (e.app k) y)
  obtain ⟨j, b, rfl⟩ := (hB1 q F _ hc (n - 1) i).1 a (unit_of o hq)
  change PP q i (n - 1) ψ (PP q i (n - 1) (s.app j) b) = _ at ha
  obtain ⟨l, g, hl⟩ := (hB1 q G _ hG (n - 1) i).2 (IsFiltered.max j k)
    (PP q i (n - 1) (G.map (IsFiltered.rightToMax j k)) y -
      PP q i (n - 1) (F.map (IsFiltered.leftToMax j k) ≫ p.app _) b) (unit_of (t.app _ ≫ p.app _) hq) (by
    change PP q i (n - 1) (e.app _) _ = 0
    rw [map_sub, ← PP_comp, ← PP_comp, he, Category.assoc, hpe, ← Category.assoc, hs, PP_comp, ha, sub_self])
  change PP q i (n - 1) (G.map g) _ = 0 at hl
  rw [map_sub, sub_eq_zero, ← PP_comp, ← PP_comp, ← G.map_comp, Category.assoc, ← p.naturality g,
    ← Category.assoc, PP_comp q i (n - 1) _ (p.app l)] at hl
  refine ⟨F.obj l, t.app l, s.app l, G.obj l, v l, p.app l, hpo l, (hts l).1, (hts l).2, ?_⟩
  rw [RP_comp q i n φ' (t.app k) (v k) (p.app k) (hpo k).w (F.map (IsFiltered.rightToMax j k ≫ g))
    (G.map (IsFiltered.rightToMax j k ≫ g)) (p.app l) (p.naturality _).symm _ _ _ (hnat _) (hv _ _ _), ← hy, RP_bd, hl]
  exact bd_pull ..

end LateralTheory.E.KernelLocalization
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) :
    pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s := pullback.fst _ _

abbrev tY {Y B S : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) (t : S ⟶ U.left) : pullback p (t ≫ U.hom) ⟶ YU p U :=
  pullback.map p (t ≫ U.hom) p U.hom (𝟙 Y) t (𝟙 B) (by simp) (by simp)

abbrev tW {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) :
    pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (tY p U t) (𝟙 W) (𝟙 B) (by simp only [tY, pullback.lift_snd_assoc, Category.assoc]; erw [Category.comp_id]) (by simp)

abbrev rT (q : ℕ) (i : ℤ) {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) (m : ℤ) :=
  rpl q i (prU p ι U) (prS p ι (t ≫ U.hom)) (tW p ι U t) (tY p U t) (pullback.lift_fst _ _ _).symm m

def LeafKillPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → rT q i p ι U t m z = 0) →
  Cov U (fun _ a => rY q i p ι a m z = 0)

def LeafPtW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B), IsProper p → ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → ¬ (Set.range s ⊆ V) →
  ∀ m, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafPtV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y Y' : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B) (g : Y' ⟶ Y), IsProper p → IsProper (g ≫ p) → ∀ (U : B.Etale) (A : Type) [CommRing A]
  (t : Sp A ⟶ U.left), SH A → Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B) → ∀ (m : ℤ), pl q i (fibMap g p (t ≫ U.hom)) m = 0 →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, rT q i (g ≫ p) ι U t m (gY q i p g ι U m y) = 0

theorem LeafKill2_of (hPt : LeafKillPt) (hW : LeafPtW) (hV : LeafPtV) : LeafKill2 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 toK ι _ V hVW p g1 g2 hp hp1 hp2 hS U y
  refine hPt hH q k hq i toK ι (g1 ≫ p) hp1 U 2 _ ?_
  intro A _ t hA
  by_cases hc : Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B)
  · exact hV hH q k hq i toK ι V hVW p g1 hp hp1 U A t hA hc 2 (hS A (t ≫ U.hom) hA hc).2.1 y
  · have := hW hH q k hq i toK ι V hVW (g1 ≫ p) hp1 A (t ≫ U.hom) hA hc 2
    exact Subsingleton.elim _ _

end LateralTheory.E.SecondDegreeKilling
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShIsoPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves

theorem Cov.bind {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' (a : U' ⟶ U), P U' a → Cov U' (fun U'' b => Q U'' (b ≫ a))) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  let R : Sieve U :=
    { arrows := fun Z c => ∀ (W : B.Etale) (d : W ⟶ Z), Q W (d ≫ c)
      downward_closed := fun {Z Z'} c hc e W d => by simpa [Category.assoc] using hc W (d ≫ e) }
  refine ⟨R, (EtTop B).transitive hS R ?_, fun U' a ha => by simpa using ha U' (𝟙 _)⟩
  intro Y f hf
  obtain ⟨S', hS', hQ⟩ := hPQ Y f (hP Y f hf)
  refine (EtTop B).superset_covering ?_ hS'
  intro Z c hc W d
  simpa [Category.assoc] using hQ W (d ≫ c) (S'.downward_closed hc d)

abbrev H0 (B : Scheme.{0}) (q : ℕ) := DerivedCategory.homologyFunctor (SShv B q) 0

def EtaleDerivedDegreeZeroHomologyLocallyLifts : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (t : (H0 B q).obj ((OU B q).obj U) ⟶ (H0 B q).obj M),
  Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ M, (H0 B q).map ((OU B q).map a) ≫ t = (H0 B q).map x)

def EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (x : (OU B q).obj U ⟶ M), (H0 B q).map x = 0 → Cov U (fun U' a => (OU B q).map a ≫ x = 0)

def LeafSheafIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (F G : SShv B q) (g : F ⟶ G),
  (∀ (U : B.Etale) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F), t ≫ g = 0 →
    Cov U (fun U' a => (H0 B q).map ((OU B q).map a) ≫ t = 0)) →
  (∀ (U : B.Etale) (s : (H0 B q).obj ((OU B q).obj U) ⟶ G),
    Cov U (fun U' a => ∃ t : (H0 B q).obj ((OU B q).obj U') ⟶ F, (H0 B q).map ((OU B q).map a) ≫ s = t ≫ g)) →
  IsIso g

theorem LeafShIso_of (hL : EtaleDerivedDegreeZeroHomologyLocallyLifts) (hK : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes) (hS : LeafSheafIso) : LeafShIso := by
  intro B q L K ℓ m hinj hsurj
  set f := (shiftFunctor (DerivedCategory (SShv B q)) m).map ℓ with hf
  have key : IsIso ((H0 B q).map f) := by
    apply hS
    · intro U t ht
      refine Cov.bind (hL B q _ U t) ?_
      rintro U' a ⟨x, hx⟩
      have h1 : (H0 B q).map (x ≫ f) = 0 := by
        rw [Functor.map_comp, ← hx, Category.assoc, ht, comp_zero]
      have h2 := hinj U' x 0 ((hK B q _ U' _ h1).mono (fun U'' b hb => by simpa using hb))
      refine h2.mono (fun U'' b hb => ?_)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hx, ← Functor.map_comp, hb, comp_zero,
        Functor.map_zero]
    · intro U s
      refine Cov.bind (hL B q _ U s) ?_
      rintro U' a ⟨y, hy⟩
      refine (hsurj U' y).mono (fun U'' b ⟨x, hx⟩ => ⟨(H0 B q).map x, ?_⟩)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hy, ← Functor.map_comp, hx, Functor.map_comp]
  have e := ((H0 B q).isoShift m)
  exact (NatIso.isIso_map_iff e ℓ).1 key

end LateralTheory.E.LeafShIsoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SimplicialPieceRelations
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf

namespace LateralTheory.E.SimplicialPieceRelations

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
abbrev HC (R : Type) [CommRing R] := HomotopyCategory (Shv R) (ComplexShape.up ℤ)

def Disc0 : Prop := ∀ (R : Type) [CommRing R] {X Y : PSh} (f : X ⟶ Y),
  ∃ (a : (Qt R).obj ((chains R).obj (disc.obj X)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj X)))
    (b : (Qt R).obj ((chains R).obj (disc.obj Y)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj Y))),
    (Qt R).map ((chains R).map (disc.map f)) ≫ b.hom = a.hom ≫ (Qt R).map ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f))

variable {R : Type} [CommRing R]

theorem relY_conj_imp (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g → Tri.RelY (Yres R F) n g' := by
  have hg' : g' = a.inv ≫ g ≫ b.hom := by rw [h]; simp
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨x, hx⟩ := hs (a.hom ≫ y)
    refine ⟨b.inv ≫ x, ?_⟩
    simp only at hx ⊢
    rw [hg']; simp [hx]
  · simp only at hx
    rw [hg'] at hx
    have : g ≫ (b.hom ≫ x1) = g ≫ (b.hom ≫ x2) := by
      have := congrArg (fun z => a.hom ≫ z) hx
      simpa using this
    have := hi this
    simpa using congrArg (fun z => b.inv ≫ z) this

theorem relY_conj (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g ↔ Tri.RelY (Yres R F) n g' :=
  ⟨relY_conj_imp F n g g' a b h, relY_conj_imp F n g' g a.symm b.symm (by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← h]; simp)⟩

def yIso (F : Shv R) (p m c : ℤ) (hc : m + p = c) : Yres R F c ≅ (Yres R F m)⟦p⟧ :=
  (Qt R).mapIso ((shiftFunctorAdd' (Cx R) m p c hc).app (res R F)) ≪≫ ((Qt R).commShiftIso p).app _

theorem relY_shift (F : Shv R) (k p : ℤ) {A B : HC R} (g : A ⟶ B) :
    Tri.RelY (Yres R F) k g → Tri.RelY (Yres R F) (k + p) (g⟦p⟧') := by
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · let e := yIso F p (k - 1) (k + p - 1) (by omega)
    obtain ⟨z, hz⟩ := (shiftFunctor (HC R) p).map_surjective (y ≫ e.hom)
    obtain ⟨w, hw⟩ := hs z
    refine ⟨(shiftFunctor (HC R) p).map w ≫ e.inv, ?_⟩
    simp only at hw ⊢
    rw [← Category.assoc, ← Functor.map_comp, hw, hz]; simp
  · let e := yIso F p k (k + p) rfl
    obtain ⟨w1, hw1⟩ := (shiftFunctor (HC R) p).map_surjective (x1 ≫ e.hom)
    obtain ⟨w2, hw2⟩ := (shiftFunctor (HC R) p).map_surjective (x2 ≫ e.hom)
    simp only at hx
    have h1 : (shiftFunctor (HC R) p).map (g ≫ w1) = (shiftFunctor (HC R) p).map (g ≫ w2) := by
      rw [Functor.map_comp, Functor.map_comp, hw1, hw2, ← Category.assoc, ← Category.assoc, hx]
    have h2 := hi ((shiftFunctor (HC R) p).map_injective h1)
    have : x1 ≫ e.hom = x2 ≫ e.hom := by rw [← hw1, ← hw2, h2]
    simpa using congrArg (fun z => z ≫ e.inv) this

theorem chains_f (U E : Spc) (u : U ⟶ E) (p : ℕ) :
    ((chains R).map u).f (-(p : ℤ)) =
      (chainsXIso R U p).hom ≫ (free R).map (u.app (Opposite.op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl]
  rfl

theorem piece_of (hD : Disc0) : Piece := by
  intro R _ F U E u p k h
  let f := u.app (Opposite.op (SimplexCategory.mk p))
  let s0 := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)
  have h1 : Tri.RelY (Yres R F) k ((Qt R).map ((chains R).map (disc.map f))) := (relK_iff R _ F k).1 h
  obtain ⟨a, b, hab⟩ := hD R f
  have h2 : Tri.RelY (Yres R F) k ((Qt R).map s0) := (relY_conj F k _ _ a b hab).1 h1
  have h3 := relY_shift F k (p : ℤ) _ h2
  have h4 : Tri.RelY (Yres R F) (k + p) ((Qt R).map (s0⟦(p : ℤ)⟧')) :=
    (relY_conj F _ _ _ (((Qt R).commShiftIso (p : ℤ)).app _) (((Qt R).commShiftIso (p : ℤ)).app _)
      (((Qt R).commShiftIso (p : ℤ)).hom.naturality s0)).2 h3
  let Eo := (CochainComplex.singleFunctors (Shv R)).shiftIso (p : ℤ) (-(p : ℤ)) 0 (by omega)
  have h5 : Tri.RelY (Yres R F) (k + p) ((Qt R).map ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map ((free R).map f))) :=
    (relY_conj F _ _ _ ((Qt R).mapIso (Eo.symm.app _)) ((Qt R).mapIso (Eo.symm.app _)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact Eo.inv.naturality _)).2 h4
  refine (relK_iff R _ F (k + p)).2 ?_
  refine (relY_conj F _ _ _ ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R U p)))
    ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))) ?_).2 h5
  simp only [piece, Functor.mapIso_hom, ← Functor.map_comp, chains_f]
  simp [f]
  rfl

end LateralTheory.E.SimplicialPieceRelations
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpecAICPf
section
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.SpecAICPf

theorem aic_equiv {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A') (h : AIC A) : AIC A' := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have := congrArg e ha
  rw [eval_map, ← coe_eval₂RingHom, map_zero] at this
  rw [← this]
  simp [eval₂_eq_sum_range, eval_eq_sum_range, map_sum]

theorem card_roots_of_aic {A : Type} [CommRing A] [IsDomain A] (h : AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.Monic → p.natDegree = n → Multiset.card p.roots = n := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    rw [eq_one_of_monic_natDegree_zero hp hn]; simp
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    have e := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (p /ₘ (X - C a)).Monic := Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [e]; exact hp)
    rw [← e, roots_mul (by rw [e]; exact hp.ne_zero), roots_X_sub_C, Multiset.card_add, ih _ hq hdeg]
    simp; omega

theorem aic_localization {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
    [IsLocalization M S] (h : AIC B) : AIC S := by
  classical
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M (Finset.image p.coeff (Finset.range (p.natDegree + 1)))
  set r : S := algebraMap B S b
  have hl : p.scaleRoots r ∈ lifts (algebraMap B S) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · obtain ⟨t, ht⟩ := hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      refine ⟨t * b ^ (p.natDegree - (i + 1)), ?_⟩
      rw [map_mul, ht, map_pow, Algebra.smul_def]
      simp only [r]
      have : p.natDegree - i = (p.natDegree - (i + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    · subst hi; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff r).2 hp)
  obtain ⟨β, hβ⟩ := h q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  have hru : IsUnit r := IsLocalization.map_units S b
  refine ⟨algebraMap B S β * hru.unit⁻¹, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := p) (RingHom.id S) (algebraMap B S β * hru.unit⁻¹) r
  simp only [eval₂_id, RingHom.id_apply] at h1
  have h2 : r * (algebraMap B S β * hru.unit⁻¹) = algebraMap B S β := by
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]
  rw [h2, ← hq, eval_map, eval₂_hom, hβ, map_zero] at h1
  exact (hru.pow _).mul_right_eq_zero.1 h1.symm

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

theorem roots_eq {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] (hK : Function.Injective (algebraMap R K)) (L : Subalgebra R K) (hL : AIC L)
    (p : R[X]) (hp : p.Monic) : (p.map (algebraMap R L)).roots.map L.val.toRingHom = (p.map (algebraMap R K)).roots ∧
      Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    exact hK (congrArg Subtype.val hab)
  have hc : Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
    rw [card_roots_of_aic hL _ _ (hp.map _) rfl, natDegree_map_eq_of_injective hinj]
  refine ⟨?_, hc⟩
  rw [roots_map_of_injective_of_card_eq_natDegree (f := L.val.toRingHom) Subtype.val_injective
    (by rw [hc, natDegree_map_eq_of_injective hinj]), map_map]
  rfl

theorem aic_of_local {R : Type} [CommRing R] [IsDomain R]
    (h : ∀ v : MaximalSpectrum R, AIC (Localization.AtPrime v.asIdeal)) : AIC R := by
  classical
  intro p hp hd
  let K := FractionRing R
  let L : MaximalSpectrum R → Subalgebra R K := fun v =>
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  have hL : ∀ v, AIC (L v) := fun v =>
    aic_equiv (IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (L v)).toRingEquiv (h v)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨e0, c0⟩ := roots_eq (IsFractionRing.injective R K) (L ⟨m, hm⟩) (hL _) p hp
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (p.map (algebraMap R K)).roots := by
    rw [← e0]
    apply Multiset.exists_mem_of_ne_zero
    intro h0
    rw [Multiset.map_eq_zero] at h0
    rw [h0] at c0; simp at c0; omega
  have hmem : x ∈ (⊥ : Subalgebra R K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot R K, Algebra.mem_iInf]
    intro v
    rw [← (roots_eq (IsFractionRing.injective R K) (L v) (hL v) p hp).1] at hx
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
    exact y.2
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hmem
  refine ⟨a, ?_⟩
  have hr := (mem_roots (hp.map _).ne_zero).1 hx
  rw [IsRoot, eval_map, eval₂_hom] at hr
  exact (IsFractionRing.injective R K) (by rw [hr, map_zero])

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

open CategoryTheory AlgebraicGeometry

theorem stalk_aic (B : CommRingCat.{0}) (hA : AIC B) (x : Spec B) : AIC ((Spec B).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra B ((Spec B).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have : IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal := StructureSheaf.IsLocalization.to_stalk B x
  exact aic_localization x.asIdeal.primeCompl hA

theorem SpecAIC_of : LateralTheory.E.FibreEqvPf.SpecAIC := by
  intro B hB hA
  refine ⟨inferInstance, ?_⟩
  intro U hU hne
  haveI : Nonempty U := hne.to_subtype
  apply aic_of_local
  intro v
  let y : PrimeSpectrum Γ(Spec B, U) := ⟨v.asIdeal, v.isMaximal.isPrime⟩
  have hy : hU.fromSpec y ∈ U := by
    show hU.fromSpec y ∈ (U : Set (Spec B))
    rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk (Spec B).presheaf ⟨hU.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime ((Spec B).presheaf.stalk (hU.fromSpec y)) y.asIdeal := hU.isLocalization_stalk' y hy
  have hst := stalk_aic B hA (hU.fromSpec y)
  exact aic_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl ((Spec B).presheaf.stalk (hU.fromSpec y))
    (Localization.AtPrime v.asIdeal)).toRingEquiv hst

end LateralTheory.E.SpecAICPf
end
end

