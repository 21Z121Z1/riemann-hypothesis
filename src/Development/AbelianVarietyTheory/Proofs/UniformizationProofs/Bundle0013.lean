import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionKernel

theorem mem_map_of_flat {R B : Type} [CommRing R] [CommRing B] (c : R →+* B) (hf : c.Flat)
    {I : Ideal R} {ε : R} (h : ∀ x, ε * x = 0 → x ∈ I) (b : B) (hb : c ε * b = 0) :
    b ∈ I.map c := by
  letI := c.toAlgebra
  haveI : Module.Flat R B := hf
  obtain ⟨l, d, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := B)
    (f := fun _ : Unit => ε) (x := fun _ => b)
    (by rw [Fintype.sum_unique, Algebra.smul_def]; exact hb)
  have : b = ∑ j, d () j • y j := hy ()
  rw [this]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem c (h _ ?_))
  have h := hc j
  rwa [Fintype.sum_unique] at h

variable {X Y : Scheme.{0}}

theorem app_rs (i : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (i.app V).hom (rs X h a) = rs Y (i.preimage_mono h) ((i.app U).hom a) := by
  have := congr(($(i.naturality (homOfLE h).op)).hom a)
  exact this

theorem gs_sub (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem gs_of_app_eq_zero (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U))
    (ha : (r.app U).hom a = 0) : gs r z U a = 0 := by rw [gs_eq r z U h, ha, map_zero]

theorem exists_rs_eq_zero {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom a = 0) :
    ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ rs X hV a = 0 := by
  obtain ⟨V, hxV, i, i', e⟩ := X.presheaf.germ_eq x hx hx a 0 (h.trans (map_zero _).symm)
  exact ⟨V, i.le, hxV, e.trans (map_zero _)⟩

variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}

theorem cst_eq (f : X ⟶ Spec (CommRingCat.of A)) (W : X.Opens) :
    SmallExtLift.cst f W = cst f W := rfl

theorem mul_eq_zero_iff_app (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {V : X.Opens} (hV : IsAffineOpen V)
    (u : Γ(X, V)) : cst f V a * u = 0 ↔ (j.app V).hom u = 0 := by
  rw [← cst_eq]
  constructor
  · intro h
    have h := mem_map_of_flat _ (SmallExtLift.cst_flat f hV) (fun x hx => (ha x).1 hx) u h
    refine (show _ ≤ RingHom.ker (j.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) h
    rw [Ideal.mem_comap, RingHom.mem_ker, SmallExtLift.app_cst P.w, RingHom.mem_ker.1 hr, map_zero]
  · intro h
    exact SmallExtLift.mul_eq_zero_of_mem _ (fun x hx => (mul_comm _ _).trans ((ha x).2 hx))
      (SmallExtLift.mem_of_app_eq_zero hg P hV u h)

theorem gs_mul_eq_zero_iff (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {W : X.Opens} (z : Y) (hz : j z ∈ W)
    (u : Γ(X, W)) : gs (𝟙 X) (j z) W (cst f W a * u) = 0 ↔ gs j z W u = 0 := by
  constructor
  · intro h
    rw [gs_eq (𝟙 X) (j z) W hz] at h
    obtain ⟨V, hV, hx, e⟩ := exists_rs_eq_zero hz (cst f W a * u) h
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have e' := congrArg (rs X hle) e
    rw [rs_rs, map_mul, rs_cst, map_zero] at e'
    rw [← gs_res j z (hle.trans hV) hx']
    exact gs_of_app_eq_zero j z V' hx' _ ((mul_eq_zero_iff_app hg ha P hA _).1 e')
  · intro h
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g₀)) :=
      IsClosedImmersion.spec_of_surjective _ hg
    have : IsClosedImmersion j := MorphismProperty.of_isPullback P.flip this
    rw [gs_eq _ _ W hz] at h
    obtain ⟨O, hO, hx, e⟩ := exists_rs_eq_zero (U := j ⁻¹ᵁ W) hz _ h
    obtain ⟨D, hD, hD'⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp O.isOpen
    have hx₁ : j z ∈ W ⊓ ⟨D, hD⟩ := ⟨hz, show z ∈ j ⁻¹' D from hD' ▸ hx⟩
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx₁
    have l : j ⁻¹ᵁ V' ≤ O := fun y hy => by
      have : y ∈ j ⁻¹' D := (hle hy).2
      rwa [hD'] at this
    have e' := congrArg (rs Y l) e
    rw [rs_rs, map_zero] at e'
    have h₂ := (mul_eq_zero_iff_app hg ha P hA (rs X (hle.trans inf_le_left) u)).2
      ((app_rs j _ u).trans e')
    rw [← gs_res (𝟙 X) (j z) (hle.trans inf_le_left) hx']
    refine gs_of_app_eq_zero (𝟙 X) (j z) V' hx' _ ?_
    change rs X _ _ = 0
    rw [map_mul, rs_cst, h₂]

theorem surjective_of_isNilpotent (hg : Function.Surjective g₀)
    (hn : IsNilpotent (RingHom.ker g₀))
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) : Function.Surjective j := by
  have h2 : Surjective (Spec.map (CommRingCat.ofHom g₀)) := ⟨fun x => by
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g₀ : Set A) := fun a ha =>
      x.isPrime.mem_of_pow_mem n (by
        have := Ideal.pow_mem_pow ha n
        rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
        rw [this]
        exact zero_mem _)
    rw [← range_comap_of_surjective _ g₀ hg] at hx
    exact hx⟩
  have : Surjective j := MorphismProperty.of_isPullback P.flip h2
  exact j.surjective

theorem exists_sec_of_local {N : LB X} {N₀ : LB Y} (w : LB.Iso N₀ (N.pull j)) (hN₀ : N₀.IsLB)
    (hw : w.IsGen) {I : Type} (V : I → X.Opens) (c : I → N.ι) (hc : ∀ q, V q ≤ N.U (c q))
    (cov : ∀ z : Y, ∃ q, j z ∈ V q) (u : ∀ q, Γ(X, V q))
    (hu : ∀ q q' z, j z ∈ V q → j z ∈ V q' →
      gs j z _ (u q) = (gm j z _ (N.g (c q) (c q'))).val * gs j z _ (u q')) :
    ∃ τ₀ : LB.Sec N₀, ∀ q k' z, j z ∈ V q → z ∈ N₀.U k' →
      (gw w (𝟙 _) z (c q) k').val * gs (𝟙 _) z _ (τ₀.f k') = gs j z _ (u q) := by
  have tr : ∀ q q' k' l' z, j z ∈ V q → j z ∈ V q' → z ∈ N₀.U k' → z ∈ N₀.U l' →
      (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) =
        (gm (𝟙 _) z _ (N₀.g k' l')).val * ((gw w (𝟙 _) z (c q') l')⁻¹.val * gs j z _ (u q')) := by
    intro q q' k' l' z h h' hk hl
    have e := (isGen_iff w).1 hw _ (𝟙 Y) z (c q) (c q') k' l' (hc q h) (hc q' h') hk hl
    rw [Category.id_comp] at e
    rw [hu q q' z h h', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    generalize gm j z _ (N.g (c q) (c q')) = B
    generalize gm (𝟙 Y) z _ (N₀.g k' l') = C
    generalize gw w (𝟙 Y) z (c q') l' = D
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : N₀.ι, ∃ s : Γ(Y, N₀.U k'), ∀ q z, j z ∈ V q → z ∈ N₀.U k' →
      gs (𝟙 _) z _ s = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) := by
    intro k'
    let O : I → Y.Opens := fun q => j ⁻¹ᵁ V q ⊓ N₀.U k'
    have l₁ : ∀ q, O q ≤ (N.pull j).U (fun _ => c q) ⊓ N₀.U k' := fun q x hx =>
      ⟨mem_pull.2 (hc q hx.1), hx.2⟩
    obtain ⟨b, hb⟩ : ∃ b : ∀ q, Γ(Y, O q), ∀ q z, z ∈ O q →
        gs (𝟙 _) z (O q) (b q) = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) :=
      ⟨fun q => rs Y (l₁ q) (w.s (fun _ => c q, k'))⁻¹.val *
          rs Y (inf_le_left : O q ≤ j ⁻¹ᵁ V q) ((j.app (V q)).hom (u q)), fun q z hz =>
        (gs_mul (𝟙 Y) z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_unit (𝟙 Y) z _ (l₁ q hz) _).trans
            (congrArg Units.val (map_inv _ _))))
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_pull (𝟙 Y) j z _ hz.1 _).trans
            (by rw [Category.id_comp]))))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' O (N₀.U k')
      (fun q => homOfLE inf_le_right) (fun z hz => by
        obtain ⟨q, hq⟩ := cov z
        exact Opens.mem_iSup.2 ⟨q, hq, hz⟩) b
      (fun q q' => fn_ext (V := O q ⊓ O q') fun z hz => by
        refine (gs_res (𝟙 Y) z inf_le_left hz _).trans
          (Eq.trans ?_ (gs_res (𝟙 Y) z inf_le_right hz _).symm)
        rw [hb q z hz.1, hb q' z hz.2, tr q q' k' k' z hz.1.1 hz.2.1 hz.1.2 hz.1.2,
          gm_self hN₀ (𝟙 Y) z hz.1.2, Units.val_one, _root_.one_mul])
    refine ⟨s, fun q z h₁ h₂ => ?_⟩
    have hz : z ∈ O q := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 Y) z inf_le_right hz s).symm.trans
      ((congrArg (gs (𝟙 Y) z (O q)) (hs q)).trans (hb q z hz))
  choose s hs using glue
  refine ⟨⟨s, fun k' l' => fn_ext fun z hz => ?_⟩, fun q k' z h₁ h₂ => ?_⟩
  · obtain ⟨q, hq⟩ := cov z
    refine (gs_res (𝟙 Y) z _ hz _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 Y) z _ hz _) (gs_res (𝟙 Y) z _ hz _))).symm)
    rw [hs k' q z hq hz.1, hs l' q z hq hz.2]
    exact tr q q k' l' z hq hq hz.1 hz.2
  · change _ * gs (𝟙 Y) z _ (s k') = _
    rw [hs k' q z h₁ h₂, Units.mul_inv_cancel_left]

theorem exists_sec_of_vanishing : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → ∀ σ : LB.Sec N, (∀ k, (β.app (N.U k)).hom (σ.f k) = 0) → ∃ τ₀ : LB.Sec N₀, ∀ τ : LB.Sec N, (∀ z (k : (N).ι) (k' : (N₀).ι), (j₀) z ∈ (N).U k → z ∈ (N₀).U k' → gs (j₀) z _ ((τ).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ₀).f k')) → ∀ k, σ.f k = cst f (N.U k) a * τ.f k := by
  intro A A₀ A' _ _ _ g₀ g' a hg hg' hn hk _ ha X Y X' f f₀ f' j β _ P P' N N₀ w hN hN₀ hw σ hσ
  let I := {q : Σ (_ : N.ι) (W : X.Opens), Γ(X, W) //
    ∃ h : q.2.1 ≤ N.U q.1, rs X h (σ.f q.1) = cst f q.2.1 a * q.2.2}
  let V : I → X.Opens := fun q => q.1.2.1
  let c : I → N.ι := fun q => q.1.1
  let u : ∀ q, Γ(X, V q) := fun q => q.1.2.2
  have hc : ∀ q, V q ≤ N.U (c q) := fun q => q.2.1
  have hu : ∀ q, rs X (hc q) (σ.f (c q)) = cst f (V q) a * u q := fun q => q.2.2
  have loc : ∀ k x, x ∈ N.U k → ∃ q, c q = k ∧ x ∈ V q := by
    intro k x hx
    obtain ⟨W, hW, hxW, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have h := SmallExtLift.mem_of_app_eq_zero hg' P' hW (rs X hle (σ.f k))
      (by rw [app_rs, hσ, map_zero])
    rw [hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨⟨⟨k, W, b⟩, hle, hb⟩, rfl, hxW⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_sec_of_local w hN₀ hw V c hc (fun z => by
      obtain ⟨k, hk⟩ := exists_chart hN (j z)
      obtain ⟨q, -, hq⟩ := loc k _ hk
      exact ⟨q, hq⟩) u (fun q q' z h h' => by
      have hm : j z ∈ V q ⊓ V q' := ⟨h, h'⟩
      have e := (gs_mul_eq_zero_iff hg ha P z hm (rs X inf_le_left (u q) -
        rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * rs X inf_le_right (u q'))).1 (by
          refine gs_of_app_eq_zero (𝟙 X) (j z) _ hm _ ?_
          change (_ : Γ(X, V q ⊓ V q')) = 0
          have e₁ := congrArg (rs X (inf_le_left : V q ⊓ V q' ≤ _)) (hu q)
          have e₂ := congrArg (rs X (inf_le_right : V q ⊓ V q' ≤ _)) (hu q')
          have e₃ := congrArg (rs X (inf_le_inf (hc q) (hc q'))) (σ.compat (c q) (c q'))
          simp only [map_mul, rs_rs, rs_cst] at e₁ e₂ e₃
          change cst f (V q ⊓ V q') a * (_ - _ * _) = 0
          linear_combination e₃ - e₁ + rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * e₂)
      rw [gs_sub _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm,
        gs_unit j z (N.U (c q) ⊓ N.U (c q')) ⟨hc q h, hc q' h'⟩, sub_eq_zero] at e
      exact e)
  refine ⟨τ₀, fun τ hτ k => fn_ext fun x hx => ?_⟩
  obtain ⟨z, rfl⟩ := surjective_of_isNilpotent hg hn P x
  obtain ⟨q, rfl, hq⟩ := loc k _ hx
  obtain ⟨k', hk'⟩ := exists_chart hN₀ z
  have e := (gs_mul_eq_zero_iff hg ha P z hq (u q - rs X (hc q) (τ.f (c q)))).2 (by
    rw [gs_sub _ _ _ hq, gs_res _ _ _ hq, hτ z (c q) k' hx hk', hτ₀ q k' z hq hk', sub_self])
  rw [mul_sub, ← hu, ← rs_cst f (hc q), ← map_mul, gs_sub (𝟙 X) (j z) _ hq, gs_res (𝟙 X) (j z) _ hq,
    gs_res (𝟙 X) (j z) _ hq, sub_eq_zero] at e
  exact e

end GlobalTheory.SectionKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootUnit

open TopologicalSpace

theorem gs_id {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (h : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = (Y.presheaf.germ U y h).hom a := gs_eq (𝟙 Y) y U h a

theorem gs_ne_zero {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (h : y ∈ U) {a : Γ(Y, U)} (ha : a ≠ 0) :
    gs (𝟙 Y) y U a ≠ 0 := by
  rw [gs_id y U h]
  intro e
  exact ha (germ_injective_of_isIntegral Y y h (e.trans (map_zero _).symm))

theorem exists_unit_of_stalks {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens) (a b : Γ(Y, W))
    (hb : ∀ y ∈ W, gs (𝟙 Y) y W b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y W a = v.val * gs (𝟙 Y) y W b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y W a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y W b := by
  have loc : ∀ y : W, ∃ (V : Y.Opens) (_ : y.1 ∈ V) (_ : V ≤ W) (c : Γ(Y, V)),
      ∀ z ∈ V, gs (𝟙 Y) z W a = gs (𝟙 Y) z V c * gs (𝟙 Y) z W b := by
    rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := h y hy
    obtain ⟨U, hU, c, hc⟩ := Y.presheaf.germ_exist v.val
    have hm : y ∈ U ⊓ W := ⟨hU, hy⟩
    have e : gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_right).op).hom a) =
        gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_left).op).hom c *
          (Y.presheaf.map (homOfLE inf_le_right).op).hom b) := by
      rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, hv, gs_id y U hU]
      exact congrArg (· * _) hc.symm
    rw [gs_id y _ hm, gs_id y _ hm] at e
    have e' := germ_injective_of_isIntegral Y y hm e
    refine ⟨U ⊓ W, hm, inf_le_right, (Y.presheaf.map (homOfLE inf_le_left).op).hom c, fun z hz => ?_⟩
    have := congrArg (gs (𝟙 Y) z (U ⊓ W)) e'
    rwa [gs_mul _ z _ hz, gs_res _ z inf_le_right hz, gs_res _ z inf_le_right hz] at this
  choose V hV hle c hc using loc
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _⟩) c
    (fun i j => fn_ext (V := V i ⊓ V j) fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      exact mul_right_cancel₀ (hb y (hle i hy.1)) ((hc i y hy.1).symm.trans (hc j y hy.2)))
  have key : ∀ y ∈ W, gs (𝟙 Y) y W a = gs (𝟙 Y) y W s * gs (𝟙 Y) y W b := fun y hy => by
    rw [hc ⟨y, hy⟩ y (hV _), ← hs ⟨y, hy⟩]
    exact congrArg (· * _) (gs_res (𝟙 Y) y (hle ⟨y, hy⟩) (hV ⟨y, hy⟩) s)
  have hu : IsUnit (show Γ(Y, W) from s) := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨v, hv⟩ := h y hy
    have := mul_right_cancel₀ (hb y hy) ((key y hy).symm.trans hv)
    exact (congrArg IsUnit ((gs_id y W hy _).symm.trans this)).mpr v.isUnit
  refine ⟨hu.unit, fun y hy => ?_⟩
  rw [← gs_unit _ y W hy]
  exact key y hy

theorem exists_unit_of_stalks' {Y : Scheme.{0}} [IsIntegral Y] (W U V : Y.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(Y, U)) (b : Γ(Y, V)) (hb : ∀ y ∈ W, gs (𝟙 Y) y V b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y U a = v.val * gs (𝟙 Y) y V b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y U a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y V b := by
  obtain ⟨r, hr⟩ := exists_unit_of_stalks W ((Y.presheaf.map (homOfLE hU).op).hom a)
    ((Y.presheaf.map (homOfLE hV).op).hom b)
    (fun y hy => by rw [gs_res (𝟙 Y) y hV hy]; exact hb y hy)
    (fun y hy => by rw [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy]; exact h y hy)
  refine ⟨r, fun y hy => ?_⟩
  have := hr y hy
  rwa [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy] at this

theorem sec_gs_ne_zero {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∃ j, s.f j ≠ 0) (y : Y) (i : K → L.ι)
    (hy : y ∈ LB.wchart L φ i) : gs (𝟙 Y) y (LB.wchart L φ i) (s.f i) ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (LB.wchart L φ j : Set Y).Nonempty := by
    by_contra hn
    exact hj (fn_ext (V := LB.wchart L φ j) fun x hx => absurd ⟨x, hx⟩ hn)
  obtain ⟨z, hz, hz'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen (LB.wchart L φ i).isOpen hne ⟨y, hy⟩
  refine gs_ne_zero y _ hy fun e => gs_ne_zero z _ hz hj ?_
  rw [sec_trans s (𝟙 Y) z hz hz', e, gs_id z _ hz', map_zero, mul_zero]

theorem trF_pull {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (y : Y) (i j : PUnit → L.ι) :
    trF (L := L) (K := PUnit) (fun _ => f) (fun _ => 1) (𝟙 Y) y i j =
      gm (𝟙 Y ≫ f) y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g _ _) := by
  rw [trF, Fintype.prod_unique, zpow_one]

theorem exists_gen_of_pow : ∀ (X Y : Scheme.{0}) [IsIntegral Y], (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → ∀ (L : LB X), L.IsLB → ∀ (f₁ f₂ : Y ⟶ X) (l : ℕ), 1 ≤ l → ∀ (s₁ : LB.Sec (L.pull f₁)) (s₂ : LB.Sec (L.pull f₂)) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![(l : ℤ), -(l : ℤ)])), u.IsGen → (∃ j, s₂.f j ≠ 0) → (∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J ^ l = (val u (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J ^ l) → ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![1, -1]), r.IsGen ∧ ∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J = (val r (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J := by
  intro X Y _ hN L hL f₁ f₂ l hl s₁ s₂ u _ hs H
  have l₁ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  have l₂ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1
  have main : ∀ j : Fin 2 → L.ι, ∃ r : Γ(Y, LB.wchart L ![f₁, f₂] j)ˣ, ∀ y ∈ LB.wchart L ![f₁, f₂] j,
      gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0)) (s₁.f fun _ => j 0) =
        (gm (𝟙 Y) y _ r).val *
          gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1)) (s₂.f fun _ => j 1) := by
    intro j
    exact exists_unit_of_stalks' (LB.wchart L ![f₁, f₂] j) _ _ (l₁ j) (l₂ j) _ _
      (fun y hy => sec_gs_ne_zero s₂ hs y _ (l₂ j hy))
      (fun y hy => by
        choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
        have hJ' : Good L y J := hJ
        haveI := hN y
        have as : Associated (sval s₂ (𝟙 Y) y J) (sval s₁ (𝟙 Y) y J) :=
          (Associated.pow_iff (by omega : l ≠ 0)).1 ⟨val u (𝟙 Y) y J, (_root_.mul_comm _ _).trans (H y J hJ').symm⟩
        obtain ⟨v, hv⟩ := as
        have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ j hy) (hJ'.mem (K := PUnit) (fun _ => f₁) (𝟙 Y))
        have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ j hy) (hJ'.mem (K := PUnit) (fun _ => f₂) (𝟙 Y))
        change _ = _ * sval s₁ (𝟙 Y) y J at e₁
        change _ = _ * sval s₂ (𝟙 Y) y J at e₂
        rw [e₁, e₂, ← hv]
        generalize trF (L := L) (K := PUnit) (fun _ => f₁) (fun _ => 1) (𝟙 Y) y _ _ = t₁
        generalize trF (L := L) (K := PUnit) (fun _ => f₂) (fun _ => 1) (𝟙 Y) y _ _ = t₂
        refine ⟨t₁ * v * t₂⁻¹, ?_⟩
        rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, Units.val_mul]
        ring)
  choose r hr using main
  refine ⟨⟨r⟩, fun i j => unit_ext fun y hy => ?_, fun y J hJ => hr _ y (hJ.mem ![f₁, f₂] (𝟙 Y))⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2) (gm_res _ y _ hy _))).symm)
  have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ i hy.1) (l₁ j hy.2)
  have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ i hy.1) (l₂ j hy.2)
  have hb := sec_gs_ne_zero s₂ hs y _ (l₂ j hy.2)
  rw [hr i y hy.1, hr j y hy.2, e₂, trF_pull, trF_pull, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul] at e₁
  have e := Units.ext (mul_right_cancel₀ hb e₁)
  rw [Fin.prod_univ_two]
  change gm (𝟙 Y) y _ (r i) = gm (𝟙 Y ≫ f₁) y _ (L.g (i 0) (j 0)) ^ (1 : ℤ) *
    gm (𝟙 Y ≫ f₂) y _ (L.g (i 1) (j 1)) ^ (-1 : ℤ) * gm (𝟙 Y) y _ (r j)
  rw [zpow_one, zpow_neg_one, mul_right_comm, ← e, mul_inv_cancel_right]

end GlobalTheory.RootUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeisenbergWeightSpaceIrreducible
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem heisenberg_weightSpace_irreducible : ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → ∀ (χ : T →* Fˣ) (U : Submodule F E), U ≤ Wt χ → (∀ h : A, (∀ t : T, e t h = 1) → ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = Wt χ := by
  classical
  intro F _ _ A _ _ E _ _ _ e Φ hcard hdim hmul hcomm hnd T lam hlam Wt hWt χ U hU hstab
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  haveI : Nontrivial E := ⟨⟨u, 0, hu0⟩⟩

  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have he1 : ∀ c, e 1 c = 1 := by
    intro c
    have := hel 1 1 c
    rw [_root_.mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  refine le_antisymm hU fun v hv => ?_
  obtain ⟨f, hf⟩ : ∃ f : E →ₗ[F] E, f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
  have hvs : v = ∑ a, c a • Φ a u := by
    rw [← hf, ← hc]; simp
  have hu := (hWt χ u).mp (hU huU)
  have hv' := (hWt χ v).mp hv
  have hlamΦ : ∀ (t : T) a, lam t (Φ a u) = ((χ t : F) * (e t a : F)) • Φ a u := by
    intro t a
    obtain ⟨k, hk⟩ := hlam t
    rw [hk, hcomm, smul_comm, ← map_smul, ← hk, hu, map_smul, smul_smul, mul_comm]
  have hvt : ∀ t : T, v = ∑ a, (c a * (e t a : F)) • Φ a u := by
    intro t
    have h1 := hv' t
    have h0 : (χ t : F) ≠ 0 := (χ t).ne_zero
    apply smul_right_injective E h0
    simp only
    rw [← h1]
    conv_lhs => rw [hvs]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hlamΦ, smul_smul, smul_smul]
    congr 1; ring
  have hT : (Fintype.card T : F) ≠ 0 := by
    intro h
    apply hcard
    rw [← Subgroup.card_mul_index T, Nat.cast_mul, Nat.card_eq_fintype_card, h, zero_mul]
  have hsum : (Fintype.card T : F) • v = ∑ a, (c a * ∑ t : T, (e t a : F)) • Φ a u := by
    have : (Fintype.card T : F) • v = ∑ _t : T, v := by
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this, Finset.sum_congr rfl fun t _ => hvt t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
  rw [← U.smul_mem_iff hT, hsum]
  refine U.sum_mem fun a _ => ?_
  by_cases ha : ∀ t : T, e t a = 1
  · exact U.smul_mem _ (hstab a ha u huU)
  · let ψ : T →* F :=
      { toFun := fun t => (e t a : F)
        map_one' := by simp [he1]
        map_mul' := fun s t => by simp [hel] }
    have hψ : ψ ≠ 1 := by
      intro h
      apply ha
      intro t
      apply Units.ext
      exact DFunLike.congr_fun h t
    have := sum_hom_units_eq_zero ψ hψ
    have h2 : ∑ t : T, (e t a : F) = 0 := this
    rw [h2, mul_zero, zero_smul]
    exact U.zero_mem

end GlobalTheory
end

