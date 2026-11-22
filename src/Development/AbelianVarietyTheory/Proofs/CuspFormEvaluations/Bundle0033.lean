import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0025
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0029
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramedBaseChange

theorem spec_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem spec_algHom_id (K : Type) [Field K] (T : Type) [CommRing T] [Algebra K T] :
    spMap (AlgHom.id K T).toRingHom = 𝟙 _ := by
  simp [spMap]

theorem dual_id (T : Type) [CommRing T] : dualMap (RingHom.id T) = RingHom.id _ :=
  RingHom.ext fun x => by
    show TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd = x
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pulledGroup_hom_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {W : Scheme.{0}} (a b : W ⟶ Gx x)
    (hs : a ≫ (snd (Over.mk x) Xo.univ.t.G).left = b ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : a ≫ (fst (Over.mk x) Xo.univ.t.G).left = b ≫ (fst (Over.mk x) Xo.univ.t.G).left) : a = b := by
  have hw : a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = b ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    have e1 := Over.w (snd (Over.mk x) Xo.univ.t.G)
    rw [← e1, ← Category.assoc, hs, Category.assoc]
  let a' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk a rfl
  let b' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk b hw.symm
  have e : a' = b' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext hf
    · exact Over.OverMorphism.ext hs
  exact congrArg CommaMorphism.left e

theorem refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid := spec_algHom_id c.F S
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    show spMap (dualMap (RingHom.id S)) = _
    rw [dual_id]
    simp [spMap]
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _,
    Category.id_comp _, by rw [eid]; exact (Category.id_comp _).trans (Category.comp_id _).symm, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by
    exact spec_comp φ.toRingHom ψ.toRingHom
  have edsp : spMap (dualMap (ψ.comp φ).toRingHom) =
      spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (ψ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, esp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']

theorem cancel {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (κ : T →ₐ[c.F] U) {y0 : FrPt Xo c S} {y : FrPt Xo c T} {z : FrPt Xo c U}
    (h₁ : FrMap φ y0 y) (h₂ : FrMap (κ.comp φ) y0 z) : FrMap κ y z := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (κ.comp φ).toRingHom = spMap κ.toRingHom ≫ spMap φ.toRingHom :=
    spec_comp φ.toRingHom κ.toRingHom
  have edsp : spMap (dualMap (κ.comp φ).toRingHom) =
      spMap (dualMap κ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (κ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  have hx : spMap κ.toRingHom ≫ y.x = z.x := by rw [hx2, hx1, esp, Category.assoc]
  let pm : Gx z.x ⟶ Gx y.x :=
    ((Over.homMk (spMap κ.toRingHom) hx : Over.mk z.x ⟶ Over.mk y.x) ▷ Xo.univ.t.G).left
  have hs : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have hf : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
      (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap κ.toRingHom := by
    rw [← Over.comp_left, whiskerRight_fst]
    rfl
  have hcomp : pm ≫ pm1 = pm2 := by
    apply pulledGroup_hom_ext
    · rw [Category.assoc, hs1, hs, hs2]
    · rw [Category.assoc, hf1, ← Category.assoc, hf, Category.assoc, ← esp, hf2]
  refine ⟨?_, ?_, pm, hs, hf, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    rw [← ha1 i h1', ← ha2 i h2']
    have e : pm1.appLE _ _ h1' ≫ pm.appLE _ _ h = pm2.appLE ((PPx y0.x).U i) ((PPx z.x).U i) h2' := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq hcomp _ _ _ _
    rw [← e, CommRingCat.hom_comp, RingHom.comp_apply]

theorem unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h₁ : FrMap φ y z) (h₂ : FrMap φ y z') :
    z = z' := by
  obtain ⟨x1, o1, u1, tan1, eig1, basis1, s1, gen1⟩ := z
  obtain ⟨x2, o2, u2, tan2, eig2, basis2, s2, gen2⟩ := z'
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  dsimp only at hx1 hu1 pm1 hs1 hf1 ha1 hx2 hu2 pm2 hs2 hf2 ha2
  have hx : x1 = x2 := hx1.trans hx2.symm
  subst hx
  have hu : u1 = u2 := funext fun τ => funext fun i => (hu1 τ i).trans (hu2 τ i).symm
  subst hu
  have hpm : pm1 = pm2 := pulledGroup_hom_ext _ _ (hs1.trans hs2.symm) (hf1.trans hf2.symm)
  subst hpm
  have hsf : s1.f = s2.f := funext fun i =>
    (ha1 i (chart_le pm1 hs1 i)).symm.trans (ha2 i (chart_le pm1 hs1 i))
  obtain ⟨f1, c1⟩ := s1
  obtain ⟨f2, c2⟩ := s2
  dsimp only at hsf
  subst hsf
  rfl

theorem isPullSec {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z)
    (h : ptO Xo z.x ⟶ ptO Xo y.x) (hh : h.left = spMap φ.toRingHom) :
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s := by
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := hm
  have hpm : pm = (h ▷ Xo.univ.t.G).left := by
    apply pulledGroup_hom_ext
    · rw [hs, ← Over.comp_left, whiskerRight_snd]
    · rw [hf, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hh]
  subst hpm
  intro j
  exact (ha j (chart_le _ hs j)).symm

end GlobalTheory.FramedBaseChange

namespace GlobalTheory

theorem framedPoint_baseChange_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMap (AlgHom.id c.F S) y y) ∧ (∀ (S T U : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U] [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) (y : FrPt Xo c S) (z : FrPt Xo c T) (w : FrPt Xo c U), FrMap φ y z → (FrMap ψ z w ↔ FrMap (ψ.comp φ) y w)) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMap φ y z' → z = z') ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → ∀ h : ptO Xo z.x ⟶ ptO Xo y.x, h.left = spMap φ.toRingHom → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s :=
  fun _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ y => FramedBaseChange.refl y,
     fun _ _ _ _ _ _ _ _ _ φ ψ _ _ _ h₁ =>
       ⟨fun h₂ => FramedBaseChange.trans φ ψ h₁ h₂, fun h₂ => FramedBaseChange.cancel φ ψ h₁ h₂⟩,
     fun _ _ _ _ _ _ φ _ _ _ h₁ h₂ => FramedBaseChange.unique φ h₁ h₂,
     fun _ _ _ _ _ _ φ _ _ hm h hh => FramedBaseChange.isPullSec φ hm h hh⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZhStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ)

theorem act_natCast (m : ℕ) : Xo.univ.t.act.act m = 𝟙 Xo.univ.t.G ^ m := by
  induction m with
  | zero =>
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]; exact mul_eq_left.1 h.symm
  | succ m ih => rw [Nat.cast_succ, Xo.univ.t.act.add, ih, Xo.univ.t.act.one, pow_succ]

theorem comp_list_prod {T T' : Over Xo.X} (h : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map fun x => h ≫ x).prod = h ≫ L.prod := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.prod_nil, MonObj.comp_one]
  | cons x L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem inZh_comp {T T' : Over Xo.X} (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) :
    InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := comp_list_prod Xo h (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j))
    rw [ha.2 mu hmu cm hcm i, MonObj.comp_one, List.map_ofFn] at h1
    simpa only [Function.comp_def, Category.assoc] using h1

theorem inZh_mul {T : Over Xo.X} (a a' : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a)
    (ha' : InZh Xo Λ N a') : InZh Xo Λ N (fun b => a b * a' b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [mul_pow, ha.1 b, ha'.1 b, _root_.mul_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have h2 := ha'.2 mu hmu cm hcm i
    rw [List.prod_ofFn] at h1 h2 ⊢
    have h3 : ∀ j, (a j * a' j) ≫ Xo.univ.t.act.act (cm i j) =
        (a j ≫ Xo.univ.t.act.act (cm i j)) * (a' j ≫ Xo.univ.t.act.act (cm i j)) := fun j => by
      have := Xo.univ.t.act.hom (cm i j)
      exact MonObj.mul_comp _ _ _
    simp only [h3]
    rw [Finset.prod_mul_distrib, h1, h2, _root_.mul_one]

theorem geoInj_comp {S T : Type} [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X)
    (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ) {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hz : GeoInj Xo x0 z) :
    GeoInj Xo x1 (fun i b => h ≫ z i b) := by
  intro k _ χ g hg i j hij
  let g' : ptO Xo (spMap (χ.comp ψ) ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap (χ.comp ψ)) rfl
  have hc : spMap (χ.comp ψ) = g.left ≫ h.left := by
    rw [hg, hh]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine hz k (χ.comp ψ) g' rfl (funext fun b => Over.OverMorphism.ext ?_)
  have h1 := congrArg (fun f => f.left) (congrFun hij b)
  change spMap (χ.comp ψ) ≫ (z i b).left = spMap (χ.comp ψ) ≫ (z j b).left
  rw [hc]
  simpa only [Over.comp_left, Category.assoc] using h1

theorem inZh_of_killedBy (hΛ : Λ.TrivAt l.M) {T : Over Xo.X} (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) : InZh Xo Λ N u := by
  classical
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [pow_two, pow_mul, (hu b).1, one_pow]
  · obtain ⟨k, hk, -, hk2⟩ := hΛ
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨hN, e, he⟩ := hu j
    have hv : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.La := by
      refine hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_)
      intro b _
      by_cases hb : b = j
      · subst hb; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne hb]; exact Submodule.zero_mem _
    obtain ⟨m, hm⟩ := Submodule.mem_one.1 (hmu _ hv i (Set.mem_univ i))
    have hm' : (m : E) = (k : E) * mu i j := by
      have : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = (k : E) • (Pi.single j (1 : E) : Fin n → E) := by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one] at hm
      exact hm
    have hcmk : cm i j * k = N * m := by
      apply RingOfIntegers.ext
      have h1 : ((cm i j * k : 𝓞 E) : E) = (cm i j : E) * (k : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      have h2 : ((N * m : 𝓞 E) : E) = (N : E) * (m : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      rw [h1, h2, hcm, hm']; ring
    have hM : (l.M : 𝓞 E) ∈ l.Mb := by
      have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
        rw [l.prod]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf h1).1
    have hcop : IsCoprime (k : 𝓞 E) ((l.M : 𝓞 E) ^ e) := (Nat.Coprime.cast hk).pow_right
    obtain ⟨p, q, hpq⟩ := hcop
    have hsplit : cm i j = N * (m * p) + (cm i j * q) * (l.M : 𝓞 E) ^ e := by
      linear_combination (-cm i j) * hpq + p * hcmk
    have := Xo.univ.t.act.hom (m * p)
    show u j ≫ Xo.univ.t.act.act (cm i j) = 1
    rw [hsplit, Xo.univ.t.act.add, MonObj.comp_mul,
      he _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hM e)), _root_.mul_one, Xo.univ.t.act.mul,
      ← Category.assoc, act_natCast, MonObj.comp_pow, Category.comp_id, hN, MonObj.one_comp]

end GlobalTheory.ZhStable

namespace GlobalTheory

theorem inZh_geoInj_stable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N (fun b => h ≫ a b)) ∧ (∀ (T : Over Xo.X) (a a' : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N a' → InZh Xo Λ N (fun b => a b * a' b)) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ (J : Type) (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)), GeoInj Xo x0 z → GeoInj Xo x1 (fun i b => h ≫ z i b)) ∧ (Λ.TrivAt l.M → ∀ (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) → InZh Xo Λ N u) :=
  fun _ _ _ _ _ _ _ Xo _ Λ N =>
    ⟨fun _ _ h a => ZhStable.inZh_comp Xo Λ N h a, fun _ a a' => ZhStable.inZh_mul Xo Λ N a a',
      fun _ _ _ _ x0 x1 ψ h hh _ z => ZhStable.geoInj_comp Xo x0 x1 ψ h hh z,
      fun hΛ _ u => ZhStable.inZh_of_killedBy Xo Λ N hΛ u⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTwistPullBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistBaseChange

theorem eq_pullS_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') : s' = GlobalTheory.VVRank.pullS A a h s := by

  exact DVR.SecOps.sec_ext H

theorem isTwistPull_baseChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T T' : Over S) (h : T' ⟶ T) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (ψ' : T' ⊗ A ⟶ T' ⊗ A) (m' : T' ⊗ A ⟶ A) (hm' : ψ' ≫ snd T' A = m'), ψ' ≫ h ▷ A = h ▷ A ≫ ψ → ∀ (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b])), α.IsGen → α'.IsGen → LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α (h ▷ A).left) → ∀ (s : LB.Sec (LPow A L b T)) (t : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L b T')) (t' : LB.Sec (LPow A L a T')), IsTwistPull A L ψ m hm a b α s t → IsPullSec A L b (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) t t' → IsTwistPull A L ψ' m' hm' a b α' s' t' := by
  intro S A _ L hL T T' h ψ m hm ψ' m' hm' hψ a b α α' hα hα' hcorr s t s' t' hst hs ht
  obtain rfl := eq_pullS_of_isPullSec A b h hs
  obtain rfl := eq_pullS_of_isPullSec A a h ht

  have e : ψ'.left ≫ (h ▷ A).left = (h ▷ A).left ≫ ψ.left := by
    rw [← Over.comp_left, hψ, Over.comp_left]
  refine GlobalTheory.VVRank.isTwistPull_of_sv A hL hα' (fun y J hJ => ?_)

  have hv : val α' (𝟙 _) y J = val α (𝟙 _ ≫ (h ▷ A).left) y J :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ hcorr _).trans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ α _ _)
  rw [GlobalTheory.VVRank.sv_pullS A a h t _ y hJ, GlobalTheory.VVRank.sv_pullS A b h s _ y hJ,
    GlobalTheory.VVRank.sv_of_isTwistPull A hst _ y hJ, hv]
  simp only [Category.id_comp, e]

end GlobalTheory.TwistBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SymmetricLiftOddOrderActsAsTranslation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem rd_fock_of_symLift : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  intro S A _ _ L x0 g Φ hχ k n U x δ s s' θ hn hδ hnx hU hact hrd

  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_thetaConstant_of_thetaGroup S A L x0 g Φ k U x hU.1
  have hread := GlobalTheory.T.reading_of_thetaGroup_action S A L x0 g Φ k U x c s s' θ hc hact hrd

  have hsq : c ^ 2 = 1 := GlobalTheory.T.thetaConst_symmetric_square_eq_one S A L x0 g Φ k U x c hc hU.3

  have hmem : (n : ℂ) • x ∈ Φ.lat := by
    rw [hnx, two_smul]
    exact add_mem hδ hδ
  have hχδ : Φ.χ ((2 : ℂ) • δ) = 1 := (GlobalTheory.T.appellHumbert_frame_semicharacter S A L x0 g Φ).2.2 hχ δ hδ
  have hpow := GlobalTheory.T.thetaConstant_pow_eq_one_of_power_trivial S A L x0 g Φ k n U x c hc hmem hU.2
  rw [hnx, hχδ, one_zpow, _root_.mul_one] at hpow

  have hc1 : c = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, hsq, one_pow, _root_.one_mul] at hpow
    exact hpow
  subst hc1
  simpa only [_root_.one_mul] using hread

end GlobalTheory.AnVal
end

