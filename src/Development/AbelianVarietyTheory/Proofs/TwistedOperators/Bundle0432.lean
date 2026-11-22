import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0073

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbases
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {T : Type} [CommRing T]
    (s : Sp (DualNumber T) ⟶ Y) (x₀ : Sp T ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber T) ⟶ X,
      spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber T) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom T T T).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber T, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  exact GlobalTheory.existsUnique_lift_of_etale_of_surjective f π hπ hnil x₀ s h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

variable {T : Type} [CommRing T]

abbrev epsBase (T : Type) [CommRing T] : Sp (DualNumber T) ⟶ Sp T := spMap (algebraMap T (DualNumber T))

abbrev epsZero (T : Type) [CommRing T] : Sp T ⟶ Sp (DualNumber T) := spMap (TrivSqZeroExt.fstHom T T T).toRingHom

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epsZero_base : epsZero T ≫ epsBase T = 𝟙 _ := by
  rw [spMap_spMap]
  exact (congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id _)

theorem eps_base (a : T) : spMap (epsMul a) ≫ epsBase T = epsBase T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsZero_eps (a : T) : epsZero T ≫ spMap (epsMul a) = epsZero T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  simp [epsMul]

theorem eps_comm (a b : T) : spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_spMap, spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, mul_left_comm]

theorem eps_cancel {a b : T} (h : a * b = 1) : spMap (epsMul a) ≫ spMap (epsMul b) = 𝟙 _ := by
  have : (epsMul a).comp (epsMul b) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, ← _root_.mul_assoc, h]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  exact Spec.map_id _

abbrev zeroAt (x : Sp T ⟶ Xo.X) : (Over.mk x : Over Xo.X) ⟶ tEps x := sec' x (epsZero T) epsZero_base

abbrev scaleAt (x : Sp T ⟶ Xo.X) (a : T) : tEps x ⟶ tEps x := res x (spMap (epsMul a)) (eps_base a)

theorem zeroAt_scaleAt (x : Sp T ⟶ Xo.X) (a : T) : zeroAt x ≫ scaleAt x a = zeroAt x :=
  Over.OverMorphism.ext (epsZero_eps a)

theorem scaleAt_comm (x : Sp T ⟶ Xo.X) (a b : T) : scaleAt x a ≫ scaleAt x b = scaleAt x b ≫ scaleAt x a :=
  Over.OverMorphism.ext (eps_comm a b)

theorem isTanAt_iff {x : Sp T ⟶ Xo.X} (a : tEps x ⟶ Xo.univ.t.G) : IsTanAt x a.left ↔ zeroAt x ≫ a = 1 :=
  ⟨fun h => Over.OverMorphism.ext h.2, fun h => ⟨Over.w a, congrArg (·.left) h⟩⟩

theorem isEigAt_iff {c : Coeff l} [Algebra c.F T] {x : Sp T ⟶ Xo.X} (τ : E →+* ℂ) (a : tEps x ⟶ Xo.univ.t.G) :
    IsEigAt c τ a.left ↔ ∀ r : 𝓞 E, a ≫ Xo.univ.t.act.act r = scaleAt x (algebraMap c.F T (embK c τ r)) ≫ a :=
  forall_congr' fun _ => ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩

theorem isCombAt_iff {x : Sp T ⟶ Xo.X} {m : ℕ} (a : Fin m → (tEps x ⟶ Xo.univ.t.G)) (cf : Fin m → T)
    (b : tEps x ⟶ Xo.univ.t.G) :
    IsCombAt x (fun i => (a i).left) cf b.left ↔ (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod = b := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain rfl : u = fun i => scaleAt x (cf i) ≫ a i := funext fun i => Over.OverMorphism.ext (hu i)
    exact Over.OverMorphism.ext h
  · intro h
    exact ⟨_, fun _ => rfl, congrArg (·.left) h⟩

variable {x x' : Sp T ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'}

def tanMap (h : IsLinHom Ψ) : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun a => Over.homMk (push Ψ (epsBase T) a) (push_hom h.1 _ a)) fun a b =>
    Over.OverMorphism.ext (h.2.1 _ _ a b _ _ rfl rfl).symm

theorem tanMap_left (h : IsLinHom Ψ) (a : tEps x ⟶ Xo.univ.t.G) : (tanMap h a).left = push Ψ (epsBase T) a := rfl

theorem tanMap_scale (h : IsLinHom Ψ) (s : T) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (scaleAt x s ≫ a) = scaleAt x' s ≫ tanMap h a :=
  Over.OverMorphism.ext (push_res Ψ _ _ a)

theorem tanMap_act (h : IsLinHom Ψ) (r : 𝓞 E) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (a ≫ Xo.univ.t.act.act r) = tanMap h a ≫ Xo.univ.t.act.act r := by
  refine Over.OverMorphism.ext ?_
  have e : toFib x (epsBase T) (a ≫ Xo.univ.t.act.act r) =
      toFib x (epsBase T) a ≫ (Over.mk x ◁ Xo.univ.t.act.act r).left := by
    rw [toFib, toFib, ← Over.comp_left, lift_whiskerLeft]
  rw [Over.comp_left, tanMap_left, tanMap_left, push, push, e, Category.assoc, reassoc_of% (h.2.2 r),
    ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  simp only [Category.assoc]

theorem sends_one (h : IsLinHom Ψ) : Sends Ψ 1 1 := by
  obtain ⟨f, hf, -⟩ := exists_pointHom h
  simpa using hf 1

theorem tanMap_zero (h : IsLinHom Ψ) {a : tEps x ⟶ Xo.univ.t.G} (ha : zeroAt x ≫ a = 1) :
    zeroAt x' ≫ tanMap h a = 1 :=
  Over.OverMorphism.ext ((sends_sec'_iff h.1 (epsZero T) epsZero_base a 1).1 (by rw [ha]; exact sends_one h))

theorem existsUnique_tanMap (h : IsLinHom Ψ) [Etale Ψ] {w : tEps x' ⟶ Xo.univ.t.G} (hw : zeroAt x' ≫ w = 1) :
    ∃! a : tEps x ⟶ Xo.univ.t.G, zeroAt x ≫ a = 1 ∧ tanMap h a = w := by
  have e₀ : ∀ (y : Sp T ⟶ Xo.X) (a : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ a = 1 ↔
      epsZero T ≫ toFib y (epsBase T) a = (lift (𝟙 (Over.mk y)) (1 : Over.mk y ⟶ Xo.univ.t.G)).left := fun y a => by
    rw [← lift_sec' y _ epsZero_base]
    refine ⟨fun e => by rw [← e], fun e => Over.OverMorphism.ext ?_⟩
    rw [← lift_l_snd (𝟙 (Over.mk y)) (_ ≫ a), e, lift_l_snd]
  have e₁ : ∀ a : tEps x ⟶ Xo.univ.t.G, tanMap h a = w ↔ toFib x (epsBase T) a ≫ Ψ = toFib x' (epsBase T) w :=
    fun a => by
      refine ⟨fun e => gx_ext ?_ ?_, fun e => Over.OverMorphism.ext ?_⟩
      · rw [Category.assoc, h.1, toFib_fst, toFib_fst]
      · rw [toFib_snd, ← e, tanMap_left, push, Category.assoc]
      · rw [tanMap_left, push, reassoc_of% e, toFib_snd]
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift Ψ (toFib x' (epsBase T) w)
    (lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ Xo.univ.t.G)).left ((sends_one h).trans ((e₀ x' w).1 hw).symm)
  have hv : v ≫ (fst (Over.mk x) Xo.univ.t.G).left = epsBase T := by rw [← h.1, reassoc_of% h₂, toFib_fst]
  let a : tEps x ⟶ Xo.univ.t.G := Over.homMk (v ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
    rw [Category.assoc, snd_hom, reassoc_of% hv]; rfl)
  have ha : toFib x (epsBase T) a = v := gx_ext (by rw [toFib_fst, hv]) (by rw [toFib_snd]; rfl)
  refine ⟨a, ⟨(e₀ x a).2 (by rw [ha, h₁]), (e₁ a).2 (by rw [ha, h₂])⟩, fun b hb => Over.OverMorphism.ext ?_⟩
  rw [← toFib_snd x _ b, hu _ ⟨(e₀ x b).1 hb.1, (e₁ b).1 hb.2⟩]
  rfl

theorem exists_basis_image {c : Coeff l} [Algebra c.F T] (h : IsLinHom Ψ) [Etale Ψ] {p : ℕ} {q : T}
    (hq : q * p = 1) (τ : E →+* ℂ) {m : ℕ} (u : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left))
    (tan : ∀ i, IsTanAt x (u i)) (eig : ∀ i, IsEigAt c τ (u i))
    (basis : ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x u a w) :
    ∃ u' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left), (∀ i, IsLieImg p Ψ (u i) (u' i)) ∧
      (∀ i, IsEigAt c τ (u' i)) ∧ ∀ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x' u' a w := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → (tEps x ⟶ Xo.univ.t.G), u = fun i => (a i).left :=
    ⟨fun i => Over.homMk (u i) (tan i).1, rfl⟩
  have c₁ : ∀ y : Sp T ⟶ Xo.X, scaleAt y q ≫ scaleAt y p = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel hq)
  have c₂ : ∀ y : Sp T ⟶ Xo.X, scaleAt y p ≫ scaleAt y q = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel ((mul_comm _ _).trans hq))
  let L : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' q ≫ tanMap h b) fun b b' => by rw [map_mul, MonObj.comp_mul]
  have hL : ∀ b, L b = scaleAt x' q ≫ tanMap h b := fun _ => rfl
  have zs : ∀ (y : Sp T ⟶ Xo.X) (s : T) (b : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ b = 1 →
      zeroAt y ≫ scaleAt y s ≫ b = 1 := fun y s b hb => by rw [← Category.assoc, zeroAt_scaleAt, hb]
  have Lz : ∀ b, zeroAt x ≫ b = 1 → zeroAt x' ≫ L b = 1 := fun b hb => zs _ _ _ (tanMap_zero h hb)
  have Ls : ∀ s b, L (scaleAt x s ≫ b) = scaleAt x' s ≫ L b := fun s b => by
    rw [hL, hL, tanMap_scale, ← Category.assoc, scaleAt_comm, Category.assoc]
  have La : ∀ r b, L (b ≫ Xo.univ.t.act.act r) = L b ≫ Xo.univ.t.act.act r := fun r b => by
    rw [hL, hL, tanMap_act, Category.assoc]
  have Li : ∀ b b', zeroAt x ≫ b = 1 → zeroAt x ≫ b' = 1 → L b = L b' → b = b' := fun b b' hb hb' e => by
    have e' := congrArg (scaleAt x' p ≫ ·) e
    simp only [hL, reassoc_of% (c₂ x')] at e'
    exact (existsUnique_tanMap h (tanMap_zero h hb')).unique ⟨hb, e'⟩ ⟨hb', rfl⟩
  have ta : ∀ i, zeroAt x ≫ a i = 1 := fun i => (isTanAt_iff _).1 (tan i)
  refine ⟨fun i => (L (a i)).left, fun i => ⟨tan i, (isTanAt_iff _).2 (Lz _ (ta i)), a i, rfl, ?_⟩,
    fun i => (isEigAt_iff τ _).2 fun r => ?_, fun w hw hw' => ?_⟩
  · exact congrArg (·.left) (show scaleAt x' p ≫ L (a i) = tanMap h (a i) by rw [hL, reassoc_of% (c₂ x')])
  · rw [← La, (isEigAt_iff τ _).1 (eig i), Ls]
  · obtain ⟨w, rfl⟩ : ∃ b : tEps x' ⟶ Xo.univ.t.G, w = b.left := ⟨Over.homMk w hw.1, rfl⟩
    obtain ⟨v, ⟨hv, e⟩, -⟩ := existsUnique_tanMap h (zs x' p w ((isTanAt_iff _).1 hw))
    obtain rfl : L v = w := by rw [hL, e, reassoc_of% (c₁ x')]
    have ev : IsEigAt c τ v.left := (isEigAt_iff τ _).2 fun r => Li _ _
      (by have := Xo.univ.t.act.hom r; rw [← Category.assoc, hv, MonObj.one_comp]) (zs _ _ _ hv)
      (by rw [La, Ls, (isEigAt_iff τ _).1 hw'])
    refine (existsUnique_congr fun cf => ?_).1 (basis _ ((isTanAt_iff _).2 hv) ev)
    have e : L (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod =
        (List.ofFn fun i => scaleAt x' (cf i) ≫ L (a i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Ls _ _)
    rw [isCombAt_iff, isCombAt_iff, ← e]
    refine ⟨congrArg L, Li _ _ (LieEtale.comp_listProd _ _ fun b hb => ?_) hv⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact zs _ _ _ (ta i)

end GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem GlobalTheory.HeckePointLawRing.exists_frame_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T]
    (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (p : ℕ), p ≠ 0 → IsLinHom Ψ → Etale Ψ →
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
      (∀ τ j, IsLieImg p Ψ (y.u τ j) (u τ j)) ∧ (∀ τ j, IsEigAt c τ (u τ j)) ∧
      ∀ τ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt x' (u τ) a w := by
  intro E _ _ _ H Dw l Xo c T _ _ y x' Ψ p hp h het
  have hF : ((p : c.F)) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hq : algebraMap c.F T ((p : c.F)⁻¹) * (p : T) = 1 := by
    rw [← map_natCast (algebraMap c.F T) p, ← map_mul, inv_mul_cancel₀ hF, map_one]
  choose u h₁ h₂ h₃ using fun τ => GlobalTheory.HeckePointLawRing.exists_basis_image (c := c) h hq τ
    (y.u τ) (y.tan τ) (y.eig τ) (y.basis τ)
  exact ⟨u, h₁, h₂, h₃⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChartPulledBackFunctionNeZeroOfValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem exists_appLE_ne_zero_of_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t₀ z J hJ hne
  refine ⟨fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left), ?_, ?_⟩
  · intro y _
    have hy : y = z := Subsingleton.elim _ _
    subst hy
    exact hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
  · intro hi
    have hz : w z ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) :=
      hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
    apply hne
    rw [sv, sval_of t₀ w z J (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) (fun _ => rfl)]
    erw [gs_eq w z _ hz]
    have hle : (⊤ : (Sp Ω).Opens) ≤ w ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) := by
      intro y _
      have hy : y = z := Subsingleton.elim _ _
      subst hy
      exact hz
    rw [← TopCat.Presheaf.germ_res_apply (Sp Ω).presheaf (homOfLE hle) z trivial]
    refine (congrArg ((Sp Ω).presheaf.germ ⊤ z trivial).hom ?_).trans (map_zero _)
    exact hi

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPair
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem sabMap_exists_iso_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {j : S' ⟶ S} (m : SABMap s' s j) :
    ∃ e : s'.G ≅ (Over.pullback j).obj s.G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst s.G.hom j = m.φ ∧
      ∀ a, s'.act.act a ≫ e.hom = e.hom ≫ (Over.pullback j).map (s.act.act a) := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback s.G _)
  have hφ' : e.hom.left ≫ pullback.fst s.G.hom j = m.φ := hφ
  refine ⟨e, he, hφ', fun a => ?_⟩
  have A : ((Over.pullback j).map (s.act.act a)).left ≫ pullback.fst s.G.hom _ =
        pullback.fst s.G.hom _ ≫ (s.act.act a).left := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, A]
    rw [reassoc_of% hφ', hφ', m.act a]
  · exact (Over.w _).trans (Over.w _).symm

theorem conj_comp_eq_id_pow {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (u : A ≅ B) (u' : A' ≅ B') [IsMonHom u.hom] (f : B ⟶ B') (f' : B' ⟶ B) (N : ℕ) (h : f ≫ f' = 𝟙 B ^ N) :
    (u.hom ≫ f ≫ u'.inv) ≫ (u'.hom ≫ f' ≫ u.inv) = 𝟙 A ^ N := by
  have : IsMonHom u.inv := inferInstance
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem pullback_map_id_pow {S S' : Scheme.{0}} (j : S' ⟶ S) (A : Over S) [GrpObj A] (N : ℕ) :
    (Over.pullback j).map (𝟙 A ^ N) = 𝟙 ((Over.pullback j).obj A) ^ N := by
  induction N with
  | zero => simpa using Functor.map_one (Over.pullback j)
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]; simp

theorem ext_of_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] (F : G.G ⟶ G'.G)
    (d : t.G ≅ Fib Xo x) (d' : t'.G ≅ Fib Xo x') [IsMonHom d.hom] [IsMonHom d'.hom]
    (e : t.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G.G)
    (e' : t'.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G'.G)
    (hd : d.hom.left ≫ pullback.fst _ _ = m₁.φ) (hd' : d'.hom.left ≫ pullback.fst _ _ = n₁.φ)
    (he : e.hom.left ≫ pullback.fst _ _ = m₂.φ) (he' : e'.hom.left ≫ pullback.fst _ _ = n₂.φ)
    (hF : (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) :
    Ext m₁ m₂ n₁ n₂ f F := by
  have A : ((Over.pullback (spMap (algebraMap T.V T.Fr))).map F).left ≫ pullback.fst G'.G.hom _ =
        pullback.fst G.G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  have B : (d.hom ≫ f ≫ d'.inv) ≫ e'.hom = e.hom ≫ (Over.pullback (spMap (algebraMap T.V T.Fr))).map F := by
    rw [hF]; simp
  refine ⟨d.hom ≫ f ≫ d'.inv, inferInstance, ?_, fun g g' h1 h2 h3 h4 => ?_⟩
  · rw [← he', ← he, Category.assoc, ← A, ← Category.assoc, ← Category.assoc e.hom.left, ← Over.comp_left,
      ← Over.comp_left, B]
  · obtain rfl : g = d.hom.left := pullback.hom_ext (h1.trans hd.symm) (h2.trans (Over.w d.hom).symm)
    obtain rfl : g' = d'.hom.left := pullback.hom_ext (h3.trans hd'.symm) (h4.trans (Over.w d'.hom).symm)
    have C : d.hom ≫ f = (d.hom ≫ f ≫ d'.inv) ≫ d'.hom := by simp
    exact congrArg (fun k => k.left) C

theorem conj_comm {C : Type*} [Category C] {A B P A' B' P' : C} (e : A ≅ P) (d : A ≅ B) (e' : A' ≅ P') (d' : A' ≅ B')
    (f : B ⟶ B') (a : A ⟶ A) (b : B ⟶ B) (p : P ⟶ P) (a' : A' ⟶ A') (b' : B' ⟶ B') (p' : P' ⟶ P')
    (hd : a ≫ d.hom = d.hom ≫ b) (he : a ≫ e.hom = e.hom ≫ p) (hd' : a' ≫ d'.hom = d'.hom ≫ b')
    (he' : a' ≫ e'.hom = e'.hom ≫ p') (h : b ≫ f = f ≫ b') :
    p ≫ (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv = ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) ≫ p' := by
  have h1 : p ≫ e.inv = e.inv ≫ a := by rw [Iso.eq_inv_comp, ← reassoc_of% he]; simp
  have h2 : b' ≫ d'.inv = d'.inv ≫ a' := by rw [Iso.eq_inv_comp, ← reassoc_of% hd']; simp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hd, reassoc_of% h, reassoc_of% h2, he']

theorem exists_ext_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' hf hf'
  have hx := semiAbelian_hom_extends_uniquely_dvr T.V T.Fr
  have inj : ∀ (s s' : SAB H (Sp T.V)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (Over.pullback (spMap (algebraMap T.V T.Fr))).map F' →
        F = F' := by
    intro s s' F F' hF hF' h
    exact (hx s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have hpow : ∀ (s : SAB H (Sp T.V)) (N : ℕ), IsMonHom (𝟙 s.G ^ N) := by
    intro s N
    induction N with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit s.G ≫ η[s.G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 s.G ^ n) (𝟙 s.G) ≫ μ[s.G]))
  obtain ⟨d, hd, hdφ, hda⟩ := sabMap_exists_iso_pullback m₁
  obtain ⟨e, he, heφ, hea⟩ := sabMap_exists_iso_pullback m₂
  obtain ⟨d', hd', hdφ', hda'⟩ := sabMap_exists_iso_pullback n₁
  obtain ⟨e', he', heφ', hea'⟩ := sabMap_exists_iso_pullback n₂
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx G.G G'.G G.semi G'.semi
    ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) (by dsimp; infer_instance)
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx G'.G G.G G'.semi G.semi
    ((e'.symm ≪≫ d').hom ≫ f' ≫ (e.symm ≪≫ d).inv) (by dsimp; infer_instance)
  have : IsMonHom (e.symm ≪≫ d).hom := by dsimp; infer_instance
  have : IsMonHom (e'.symm ≪≫ d').hom := by dsimp; infer_instance
  refine ⟨F, F', hF, hF', ext_of_map_eq m₁ m₂ n₁ n₂ f F d d' e e' hdφ hdφ' heφ heφ' hFf,
    ext_of_map_eq n₁ n₂ m₁ m₂ f' F' d' d e' e hdφ' hdφ heφ' heφ hFf', fun N h => ?_, fun N h => ?_,
    fun h a => ?_, fun h a => ?_⟩
  · refine inj _ _ _ _ inferInstance (hpow G N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f f' N h
  · refine inj _ _ _ _ inferInstance (hpow G' N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f' f N h
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf]
    exact conj_comm e d e' d' f _ _ _ _ _ _ (hda a) (hea a) (hda' a) (hea' a) (h a)
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf']
    exact conj_comm e' d' e d f' _ _ _ _ _ _ (hda' a) (hea' a) (hda a) (hea a) (h a)

end GlobalTheory.HkIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.PairBC

section General

variable {S S' : Scheme.{0}} {j : S' ⟶ S}

theorem exists_proj {X : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (w : S' ⟶ X) (h : w = j ≫ x) :
    ∃ π : pullback G.hom w ⟶ pullback G.hom x, π ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j ∧
      IsGrpPullback ((Over.pullback w).obj G) ((Over.pullback x).obj G) j π := by
  have e : pullback.fst G.hom w ≫ G.hom = (pullback.snd _ _ ≫ j) ≫ x := by
    rw [Category.assoc, ← h, pullback.condition]
  exact ⟨pullback.lift _ _ e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G _).congr h (pullback.lift_fst _ _ e).symm) (pullback.lift_snd _ _ _)⟩

theorem id_pow_left {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {π : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G j π) (N : ℕ) : (𝟙 G' ^ N).left ≫ π = π ≫ (𝟙 G ^ N).left := by
  let U : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk π h.1.w
  have e : pushHom h G' (𝟙 G') = U := Over.OverMorphism.ext (Category.id_comp π)
  have e' : pushHom h G' (𝟙 G' ^ N) = U ≫ 𝟙 G ^ N := by
    rw [map_pow, e, MonObj.comp_pow, Category.comp_id]
  exact congrArg (fun u => u.left) e'

theorem eq_iff [Flat j] [Surjective j] {A B : Over S} {A' B' : Over S'} {α : A'.left ⟶ A.left}
    {β : B'.left ⟶ B.left} (hα : IsPullback α A'.hom A.hom j) (hβ : IsPullback β B'.hom B.hom j)
    {u v : A ⟶ B} {u' v' : A' ⟶ B'} (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ β = α ≫ v.left) :
    u = v ↔ u' = v' := by
  have : Flat α := MorphismProperty.of_isPullback (P := @Flat) hα.flip ‹_›
  have : Surjective α := MorphismProperty.of_isPullback (P := @Surjective) hα.flip ‹_›
  have : Epi α := Flat.epi_of_flat_of_surjective α
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (hβ.hom_ext (hu.trans hv.symm) (by rw [Over.w, Over.w]))
  · rintro rfl
    exact Over.OverMorphism.ext ((cancel_epi α).1 (hu.symm.trans hv))

theorem comp_sq {A B C : Over S} {A' B' C' : Over S'} {α : A'.left ⟶ A.left} {β : B'.left ⟶ B.left}
    {δ : C'.left ⟶ C.left} {u : A ⟶ B} {v : B ⟶ C} {u' : A' ⟶ B'} {v' : B' ⟶ C'}
    (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ δ = β ≫ v.left) :
    (u' ≫ v').left ≫ δ = α ≫ (u ≫ v).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% hu]

theorem map_sq {X : Scheme.{0}} {G : Over X} {x : S ⟶ X} {w : S' ⟶ X} (π : pullback G.hom w ⟶ pullback G.hom x)
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _) (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j) (a : G ⟶ G) :
    ((Over.pullback w).map a).left ≫ π = π ≫ ((Over.pullback x).map a).left := by
  apply pullback.hom_ext <;>
    simp [h₁, h₂, reassoc_of% h₁, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

end General

theorem exists_isBC_and_isPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w'
  refine ⟨fun hw hw' f => ?_, fun f f' g g' N hf hf' => ?_⟩
  · obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hw
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hw'
    have e : (π ≫ f.left) ≫ (Fib Xo x').hom = (Fib Xo w).hom ≫ spMap φ :=
      (Category.assoc _ _ _).trans ((congrArg (π ≫ ·) (Over.w f)).trans hπ.1.w)
    refine ⟨Over.homMk (hπ'.1.lift _ _ e) (hπ'.1.lift_snd _ _ e), hw, hw', fun ρ ρ' q₁ q₂ q₁' q₂' => ?_⟩
    obtain rfl : ρ = π := pullback.hom_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
    obtain rfl : ρ' = π' := pullback.hom_ext (q₁'.trans p₁'.symm) (q₂'.trans p₂'.symm)
    exact hπ'.1.lift_fst _ _ e
  · have := FieldBaseChange.flat_spMap φ
    have := FieldBaseChange.surjective_spMap φ
    obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hf.1
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hf.2.1
    have e := hf.2.2 π π' p₁ p₂ p₁' p₂'
    have e' := hf'.2.2 π' π p₁' p₂' p₁ p₂
    refine and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ hπ' g f e.symm).symm
      (and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ' hπ g' f' e'.symm).symm
      (and_congr (eq_iff hπ.1 hπ.1 (comp_sq e e') (id_pow_left hπ N))
      (and_congr (eq_iff hπ'.1 hπ'.1 (comp_sq e' e) (id_pow_left hπ' N))
      (and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_)))))
    · exact eq_iff hπ.1 hπ'.1 (comp_sq (map_sq π p₁ p₂ _) e)
        (comp_sq (u := f) (u' := g) (v := (Over.pullback x').map _) (v' := (Over.pullback w').map _) e
          (map_sq π' p₁' p₂' _))
    · exact eq_iff hπ'.1 hπ.1 (comp_sq (map_sq π' p₁' p₂' _) e')
        (comp_sq (u := f') (u' := g') (v := (Over.pullback x).map _) (v' := (Over.pullback w).map _) e'
          (map_sq π p₁ p₂ _))

end GlobalTheory.HkIntegral.PairBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes → i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) := by
  first | exact @GlobalTheory.CompleteValExt.finite_and_integral | exact GlobalTheory.CompleteValExt.finite_and_integral | (intros; apply GlobalTheory.CompleteValExt.finite_and_integral <;> assumption)
end

