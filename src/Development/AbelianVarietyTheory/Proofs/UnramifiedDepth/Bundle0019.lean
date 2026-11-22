import Mathlib
import ReciprocityTheory.DualLattices.Bundle0029
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0017
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSemilinearRankNullityModMaxIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvImgIsLatSubring
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)

end

open TensorProduct IsLocalRing Matrix in

theorem _root_.GlobalTheory.evImg_isLat_subring :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  unfold _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement
  intro C _ _ hdom hinj
  classical
  letI inst : ∀ i, Algebra Tw.O.carrier (D.fin.AAx i).carrier := fun i =>
    ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
  have hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := fun t => by
    have h := (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) (_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (D.pt_p t)).choose_spec.choose_spec
    exact ⟨h.1, h.2.1⟩
  let ev : ∀ t : _root_.ReciprocityTheory.PGsh.Up.Nb p g, (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] Tw.O.carrier := fun t =>
    { toRingHom := ((D.ptMap t).1 : (D.fin.AAx (D.ptIdx t)).carrier →+* Tw.O.carrier).comp
        (Pi.evalRingHom _ (D.ptIdx t))
      commutes' := fun o => by
        have h := congrArg (fun φ : _root_.ReciprocityTheory.PGsh.LHom Tw.O Tw.O => φ.1 o) (hspec t).1
        exact h }
  let Ψ : (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → Tw.O.carrier) :=
    Pi.algHom _ _ ev
  let f : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → C) :=
    (Algebra.linearMap Tw.O.carrier C).compLeft (_root_.ReciprocityTheory.PGsh.Up.Nb p g) ∘ₗ Ψ.toLinearMap
  have hf : ∀ F x, f F x = algebraMap _ C ((D.ptMap x).1 (F (D.ptIdx x))) := fun F x => rfl
  have himg : D.evImg C = LinearMap.range f := by
    unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg _root_.ReciprocityTheory.PGsh.Be2.Dat.evAll
    change Submodule.span _ (Set.range ⇑f) = _
    rw [← LinearMap.coe_range, Submodule.span_eq]
  have hinjΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    funext i
    apply D.fin.sep i
    intro φ hφ
    have hz : p • B.map φ (D.fin.y i) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
    obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
    have ht' : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t = B.map φ (D.fin.y i) := congrArg Subtype.val ht
    obtain ⟨i0, φ0, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ hz
    obtain ⟨hi, hφ0⟩ := huniq i φ hφ rfl
    obtain ⟨hi', hψ0⟩ := huniq (D.ptIdx t) (D.ptMap t) (hspec t).1 ((hspec t).2.trans ht')
    subst hi
    have key : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), j = i → HEq ψ φ →
        ψ.1 (F j) = φ.1 (F i) := by
      rintro j ψ rfl h
      rw [eq_of_heq h]
    exact (key _ _ hi' (hψ0.trans hφ0.symm)).symm.trans (congrFun hF t)
  haveI : ∀ i, Module.Free Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).1
  haveI : ∀ i, Module.Finite Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).2
  haveI := hdom
  have hrank : Module.finrank Tw.O.carrier (∀ i, (D.fin.AAx i).carrier) = Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [Module.finrank_pi_fintype, ← Nat.card_eq_fintype_card]
    refine Eq.trans ?_ (D.fin.rank.trans (Nat.card_congr (Equiv.ofBijective _ D.L.τ_basis)).symm)
    rfl
  let b0 := Module.Free.chooseBasis Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)) =
      Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hrank]
  let b := b0.reindex (Fintype.equivOfCardEq hcard)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.PGsh.L2.IsLat
    refine ⟨Matrix.of fun x j => f (b j) x, ?_, ?_⟩
    · rw [isUnit_iff_ne_zero]
      have hdet : (Matrix.of fun x j => f (b j) x).det =
          algebraMap Tw.O.carrier C (Matrix.of fun x j => Ψ (b j) x).det := by
        rw [RingHom.map_det]; rfl
      rw [hdet]
      intro h0
      rw [← map_zero (algebraMap Tw.O.carrier C)] at h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (hinj h0)
      apply hv0
      have hsum : Ψ (∑ j, v j • b j) = 0 := by
        rw [← hv]
        funext x
        simp [Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm]
      have h1 : ∑ j, v j • b j = 0 := hinjΨ (by rw [hsum, map_zero])
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent v h1 j
    · rw [himg]
      change _ = Submodule.span _ (Set.range (f ∘ b))
      rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  · rw [himg]
    rintro _ ⟨F, rfl⟩
    exact fun x => ⟨_, (hf F x).symm⟩
  · rw [himg]
    exact ⟨1, by funext x; simp only [hf, Pi.one_apply, map_one]⟩
  · rw [himg]
    rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩
    exact ⟨F * G, by funext x; simp only [hf, Pi.mul_apply, map_mul]⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsBXOfFactorSystems
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section GroupIdentities
variable {M : Type} [CommGroup M]

private lemma mul_rearrange_five {u u' u'' a b c d : M} (h : b * a = d * c) :
    u * u' * a * u'' * b = u * (u' * u'' * c) * d := by
  calc _ = u * u' * u'' * (b * a) := by ac_rfl
    _ = u * u' * u'' * (d * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero {u a b : M} (h : b * a = b * b) : a⁻¹ * u * b = u := by
  rw [← mul_left_cancel h, mul_right_comm, inv_mul_cancel, _root_.one_mul]

private lemma fs_inter {u u' w w' a b c d e f : M} (h : a * b * c = d * e * f) :
    u * u' * e * (w * w' * f) * d = u * w * b * (u' * w' * c) * a := by
  calc _ = u * u' * w * w' * (d * e * f) := by ac_rfl
    _ = u * u' * w * w' * (a * b * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_nat {u u' a b c d e : M} (h : a * b = c * d * e) :
    u * u' * a * b = u * c * (u' * d) * e := by
  calc _ = u * u' * (a * b) := by ac_rfl
    _ = u * u' * (c * d * e) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero_nat {a b c : M} (h : a * b = b * b * c) : a⁻¹ * b = c⁻¹ := by
  have h' : a = b * c := by
    apply mul_right_cancel (b := b)
    rw [h]; ac_rfl
  rw [h', mul_inv, mul_right_comm, inv_mul_cancel, _root_.one_mul]

end GroupIdentities

private lemma fs_sigma_eq {A U : Type} {x x' y y' : A} {u u' : U} :
    (⟨x, y, u⟩ : Σ _ : A, Σ _ : A, U) = ⟨x', y', u'⟩ ↔ x = x' ∧ y = y' ∧ u = u' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma fs_units_fibre {R₀ : Type} [CommRing R₀] {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁}
    {p₂ : LHom F R₂} {f₁ : LHom R₁ R} {f₂ : LHom R₂ R} (h : IsFibreSq p₁ p₂ f₁ f₂)
    (a : (R₁ : Type)ˣ) (b : (R₂ : Type)ˣ)
    (hab : Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) a =
      Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) b) :
    ∃! c : (F : Type)ˣ, Units.map (p₁.1 : (F : Type) →* (R₁ : Type)) c = a ∧
      Units.map (p₂.1 : (F : Type) →* (R₂ : Type)) c = b := by
  obtain ⟨c, ⟨h1, h2⟩, hu⟩ := h.2.2.2 (a : R₁.carrier) (b : R₂.carrier) (congrArg Units.val hab)
  have hc : IsUnit c := p₁.2.map_nonunit c (by
    have : (p₁.1 : F.carrier →+* R₁.carrier) c = a := h1
    rw [this]; exact a.isUnit)
  refine ⟨hc.unit, ⟨Units.ext h1, Units.ext h2⟩, ?_⟩
  rintro c' ⟨e1, e2⟩
  exact Units.ext (hu c' ⟨congrArg Units.val e1, congrArg Units.val e2⟩)

theorem exists_BX_of_factorSystems :
  (∀ {R₀ : Type} [CommRing R₀] (B₀ : BX R₀) (δ : ∀ {R S : LAlg R₀}, LHom R S → B₀.G R → B₀.G R → (S : Type)ˣ)
    (t₁ t₂ : ∀ R : LAlg R₀, B₀.G R → B₀.G R → B₀.G R → (R : Type)ˣ) (w : ∀ R : LAlg R₀, B₀.G R → B₀.G R → (R : Type)ˣ),
    (∀ R x y, δ (LHom.id R) x y = 1) →
    (∀ {Q R S : LAlg R₀} (f : LHom Q R) (h : LHom R S) x y, δ (h.comp f) x y = Units.map (h.1 : (R : Type) →* (S : Type)) (δ f x y) * δ h (B₀.map f x) (B₀.map f y)) →
    (∀ R x x' x'' y, t₁ R (x + x') x'' y * t₁ R x x' y = t₁ R x (x' + x'') y * t₁ R x' x'' y) → (∀ R x x' y, t₁ R x x' y = t₁ R x' x y) →
    (∀ R x y y' y'', t₂ R x (y + y') y'' * t₂ R x y y' = t₂ R x y (y' + y'') * t₂ R x y' y'') → (∀ R x y y', t₂ R x y y' = t₂ R x y' y) →
    (∀ R x x' y y', t₁ R x x' (y + y') * t₂ R x y y' * t₂ R x' y y' = t₂ R (x + x') y y' * t₁ R x x' y * t₁ R x x' y') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x x' y, Units.map (f.1 : (R : Type) →* (S : Type)) (t₁ R x x' y) * δ f (x + x') y =
      δ f x y * δ f x' y * t₁ S (B₀.map f x) (B₀.map f x') (B₀.map f y)) →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y y', Units.map (f.1 : (R : Type) →* (S : Type)) (t₂ R x y y') * δ f x (y + y') =
      δ f x y * δ f x y' * t₂ S (B₀.map f x) (B₀.map f y) (B₀.map f y')) →
    (∀ R x y, w R x y * w R y x = 1) → (∀ R x x' y, t₁ R x x' y * w R (x + x') y = w R x y * w R x' y * t₂ R y x x') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y, Units.map (f.1 : (R : Type) →* (S : Type)) (w R x y) * δ f y x = δ f x y * w S (B₀.map f x) (B₀.map f y)) →
    ∃ (B : BX R₀) (κ : ∀ R, B.G R ≃+ B₀.G R) (b : ∀ R x y, B.P R x y),
      (∀ {R S : LAlg R₀} (f : LHom R S) x, κ S (B.map f x) = B₀.map f (κ R x)) ∧
      (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R (κ R x) (κ R x') (κ R y)) (b R (x + x') y)) ∧
      (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R (κ R x) (κ R y) (κ R y')) (b R x (y + y'))) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) x y, B.pmap f (b R x y) = B.smul (δ f (κ R x) (κ R y)) (b S (B.map f x) (B.map f y)))) := by
  intro R₀ _ B₀ δ t₁ t₂ w hid hcomp h1a h1c h2a h2c hint h1n h2n hww hw1 hwn
  let B : BX R₀ :=
    { B₀ with
      P := fun R _ _ => (R : Type)ˣ
      smul := fun l u => l * u
      one_smul := fun u => _root_.one_mul u
      mul_smul := fun l l' u => _root_.mul_assoc l l' u
      nonempty := fun _ _ _ => ⟨1⟩
      trans := fun u v => ⟨v * u⁻¹, by simp, fun l hl => by rw [← hl]; simp⟩
      pmap := fun {R S} f {x y} u => Units.map (f.1 : (R : Type) →* (S : Type)) u * δ f x y
      pmap_smul := fun f _ _ l u => by rw [map_mul, _root_.mul_assoc]
      pmap_id := fun {R x y} u => heq_of_eq (by rw [hid, _root_.mul_one]; rfl)
      pmap_comp := fun f g _ _ u => heq_of_eq (by rw [hcomp, map_mul, ← _root_.mul_assoc]; rfl)
      add1 := fun {R x x' y} u u' => u * u' * t₁ R x x' y
      add2 := fun {R x y y'} u u' => u * u' * t₂ R x y y'
      zero1 := fun {R} y => (t₁ R 0 0 y)⁻¹
      zero2 := fun {R} x => (t₂ R x 0 0)⁻¹
      addFst_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h1a _ _ _ _ _))
      addSnd_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h2a _ _ _ _ _))
      addFst_comm := fun u u' => heq_of_eq (by rw [h1c, _root_.mul_comm u])
      addSnd_comm := fun u u' => heq_of_eq (by rw [h2c, _root_.mul_comm u])
      zeroFst_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h1a R 0 0 x y))
      zeroSnd_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h2a R x 0 0 y))
      addFst_smul := fun l l' u u' => by ac_rfl
      addSnd_smul := fun l l' u u' => by ac_rfl
      interchange := fun u u' v v' => fs_inter (hint _ _ _ _ _)
      addFst_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h1n _ _ _ _))
      addSnd_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h2n _ _ _ _))
      zeroFst_nat := fun f y => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h1n f 0 0 y))
      zeroSnd_nat := fun f x => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h2n f x 0 0))
      sw := fun {R x y} u => u * w R x y
      sw_smul := fun l u => _root_.mul_assoc _ _ _
      sw_nat := fun f _ _ u => by rw [map_mul, _root_.mul_assoc, _root_.mul_assoc, hwn]
      swap_addFst := fun u u' => fs_nat (hw1 _ _ _ _)
      sw_sw := fun u => by rw [_root_.mul_assoc, hww, _root_.mul_one]
      fibre_P := by
        intro F R₁ R₂ R p₁ p₂ f₁ f₂ h
        rintro ⟨x₁, y₁, u₁⟩ ⟨x₂, y₂, u₂⟩ e
        obtain ⟨ex, ey, eu⟩ := fs_sigma_eq.1 e
        obtain ⟨x, ⟨rfl, rfl⟩, hx⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h x₁ x₂ ex
        obtain ⟨y, ⟨rfl, rfl⟩, hy⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h y₁ y₂ ey
        have hsq : f₁.comp p₁ = f₂.comp p₂ := Subtype.ext h.1
        have hδ := (hcomp p₁ f₁ x y).symm.trans (hsq ▸ hcomp p₂ f₂ x y)
        obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := fs_units_fibre h (u₁ / δ p₁ x y) (u₂ / δ p₂ x y) (by
          rw [map_div, map_div, div_eq_div_iff_mul_eq_mul]
          apply mul_right_cancel (b := δ f₁ (B₀.map p₁ x) (B₀.map p₁ y) *
            δ f₂ (B₀.map p₂ x) (B₀.map p₂ y))
          dsimp only at eu
          calc _ = (Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) u₁ *
                δ f₁ (B₀.map p₁ x) (B₀.map p₁ y)) *
                (Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) (δ p₂ x y) *
                δ f₂ (B₀.map p₂ x) (B₀.map p₂ y)) := by ac_rfl
            _ = _ := by rw [eu, ← hδ]; ac_rfl)
        refine ⟨⟨x, y, u⟩, ⟨fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩, fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩⟩, ?_⟩
        · dsimp only
          rw [hu1, div_mul_cancel]
        · dsimp only
          rw [hu2, div_mul_cancel]
        · rintro ⟨x', y', u'⟩ ⟨e1, e2⟩
          obtain ⟨a1, b1, c1⟩ := fs_sigma_eq.1 e1
          obtain ⟨a2, b2, c2⟩ := fs_sigma_eq.1 e2
          obtain rfl := hx x' ⟨a1, a2⟩
          obtain rfl := hy y' ⟨b1, b2⟩
          exact fs_sigma_eq.2 ⟨rfl, rfl, hu u' ⟨eq_div_iff_mul_eq'.2 c1, eq_div_iff_mul_eq'.2 c2⟩⟩ }
  refine ⟨B, fun R => AddEquiv.refl _, fun R _ _ => (1 : (R : Type)ˣ), fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro R x x' y
    exact show (1 : (R : Type)ˣ) * 1 * t₁ R x x' y = t₁ R x x' y * 1 by simp
  · intro R x y y'
    exact show (1 : (R : Type)ˣ) * 1 * t₂ R x y y' = t₂ R x y y' * 1 by simp
  · intro R S f x y
    exact show Units.map (f.1 : (R : Type) →* (S : Type)) 1 * δ f x y = δ f x y * 1 by simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndDifferentialRingHom
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

variable {R₀ : Type} [CommRing R₀]

private lemma endDiff_exists_lift {O R : LAlg R₀} (s : LHom O R) (i : (R : Type)) (hi : i * i = 0) :
    ∃ φ : LHom (DualNum.dualPair O).D R, φ.comp (DualNum.dualPair O).σ = s ∧
      φ.1 (DualNum.dualPair O).η = i := by
  let ψ : DualNum.DN O →ₐ[R₀] (R : Type) :=
    Ideal.Quotient.liftₐ _ (Polynomial.aevalTower s.1 i) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [pow_two, hi])
  have hσ : ∀ r, ψ ((DualNum.dualPair O).σ.1 r) = s.1 r := fun r => by
    change ψ (algebraMap (O : Type) (DualNum.DN O) r) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply]
    exact Polynomial.aevalTower_C s.1 i r
  have hη : ψ (DualNum.dualPair O).η = i := by
    change ψ (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aevalTower_X s.1 i
  refine ⟨⟨ψ, ⟨fun d hd => ?_⟩⟩, ?_, hη⟩
  · have hk : d - (DualNum.dualPair O).σ.1 ((DualNum.dualPair O).π.1 d) ∈
        RingHom.ker (DualNum.dualPair O).π.1 := by
      rw [RingHom.mem_ker, map_sub, (DualNum.dualPair O).sect, sub_self]
    rw [(DualNum.dualPair O).ker_eq] at hk
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hk
    have h1 : ψ y * i = ψ d - s.1 ((DualNum.dualPair O).π.1 d) := by
      rw [← hσ, ← hη]
      exact (map_mul ψ _ _).symm.trans ((congrArg ψ hy).trans (map_sub ψ _ _))
    have hn : IsNilpotent (-(ψ y * i)) := ⟨2, by
      rw [show (-(ψ y * i)) ^ 2 = ψ y * ψ y * (i * i) by ring, hi, mul_zero]⟩
    have hu : IsUnit (s.1 ((DualNum.dualPair O).π.1 d)) := by
      have h2 := hn.isUnit_add_left_of_commute (u := ψ d) hd (Commute.all _ _)
      rw [h1] at h2
      simpa using h2
    exact (DualNum.dualPair O).π.2.map_nonunit d (s.2.map_nonunit _ hu)
  · exact Subtype.ext (AlgHom.ext hσ)

private lemma endDiff_ηmap_surj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Surjective Dp.ηmap := by
  rintro ⟨x, hx⟩
  have hx' := hx
  rw [Submodule.restrictScalars_mem, Dp.ker_eq] at hx'
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  have hk : y - Dp.σ.1 (Dp.π.1 y) ∈ RingHom.ker Dp.π.1 := by
    rw [RingHom.mem_ker, map_sub, Dp.sect, sub_self]
  rw [Dp.ker_eq] at hk
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨Dp.π.1 y, Subtype.ext ?_⟩
  change Dp.σ.1 (Dp.π.1 y) * Dp.η = y * Dp.η
  have := Dp.η_sq
  linear_combination (-Dp.η) * (-hz) - z * this

private lemma endDiff_ηmap_inj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Injective Dp.ηmap := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  exact Dp.free r (congrArg Subtype.val hr)

private lemma endDiff_coord {g : ℕ} {V M : Type} [AddCommGroup V] [Module R₀ V] [AddCommGroup M]
    [Module R₀ M] (gb : Module.Basis (Fin g) R₀ V) :
    Function.Bijective (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) := by
  have : (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft gb).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  rw [this]
  exact (TensorProduct.equivFinsuppOfBasisLeft gb).symm.bijective.comp
    Finsupp.equivFunOnFinite.symm.bijective

private def endDiff_IsMat {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) (d : Matrix (Fin g) (Fin g) (O : Type)) : Prop :=
  ∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
    (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (d k l) * i) →
      e.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)

private lemma endDiff_exists {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) : ∃ d, endDiff_IsMat gb e d := by
  let Dp := DualNum.dualPair O
  have h1 : ∀ l, ∃ c : Fin g → (O : Type), e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c k)) := fun l => by
    have h0 : B.map Dp.π (e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk))) = 0 := by
      rw [← e.nat, (B.tg_ker Dp.π Dp.sqZero _).2 ⟨_, rfl⟩, map_zero]
    obtain ⟨v, hv⟩ := (B.tg_ker Dp.π Dp.sqZero _).1 h0
    obtain ⟨m, rfl⟩ := (endDiff_coord (M := Dp.π.ker) gb).2 v
    choose c hc using fun k => endDiff_ηmap_surj Dp (m k)
    exact ⟨c, by rw [← hv]; simp only [hc]⟩
  choose c hc using h1
  refine ⟨fun k l => c l k, ?_⟩
  intro R S s π hπ l i m hm
  have hi : (i : (R : Type)) * i = 0 := by
    have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
    rw [hπ.2] at this
    simpa using this
  obtain ⟨φ, hφ, hη⟩ := endDiff_exists_lift s (i : (R : Type)) hi
  have hs : ∀ r, φ.1 (Dp.σ.1 r) = s.1 r := fun r => by rw [← hφ]; rfl
  have hf : ∀ a ∈ Dp.π.ker, φ.1.toLinearMap a ∈ π.ker := fun a ha => by
    obtain ⟨r, hr⟩ := endDiff_ηmap_surj Dp ⟨a, ha⟩
    have : a = Dp.σ.1 r * Dp.η := (congrArg Subtype.val hr).symm
    rw [this]
    change φ.1 (Dp.σ.1 r * Dp.η) ∈ RingHom.ker π.1
    rw [map_mul, hη]
    exact Ideal.mul_mem_left _ _ i.2
  have hA : gb l ⊗ₜ[R₀] i = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (gb l ⊗ₜ[R₀] Dp.ηk) := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    exact Subtype.ext hη.symm
  have hB : ∑ k, gb k ⊗ₜ[R₀] m k = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c l k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.lTensor_tmul]
    congr 1
    refine Subtype.ext ?_
    change _ = φ.1 (Dp.σ.1 (c l k) * Dp.η)
    rw [hm k, map_mul, hη, hs]
  rw [hA, hB, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, ← hc l,
    ← e.nat, hφ]

private lemma endDiff_spec {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (l : Fin g) (r : (O : Type)) :
    e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap r)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d k l * r)) :=
  h Dp.σ Dp.π Dp.sqZero l _ _ fun k => by
    change Dp.σ.1 (d k l * r) * Dp.η = Dp.σ.1 (d k l) * (Dp.σ.1 r * Dp.η)
    rw [map_mul, _root_.mul_assoc]

private lemma endDiff_unique {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (d' : Matrix (Fin g) (Fin g) (O : Type))
    (h' : ∀ l, e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap 1)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d' k l))) : d = d' := by
  ext k l
  have h1 := B.tg_inj _ _ ((endDiff_spec h Dp l 1).symm.trans (h' l))
  have h2 := (endDiff_coord (M := Dp.π.ker) gb).1 h1
  simpa using endDiff_ηmap_inj Dp (congrFun h2 k)

theorem exists_endDifferential_ringHom :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O),
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    ∃ dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type), (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ g B O gb O₀ _ f hf
  choose d hd using fun a => endDiff_exists gb (f a)
  let Dp := DualNum.dualPair O
  have hadd : ∀ a b, d (a + b) = d a + d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).1, endDiff_spec (hd a), endDiff_spec (hd b), ← map_add,
        ← Finset.sum_add_distrib]
      simp [TensorProduct.tmul_add]
  have hone : d 1 = 1 :=
    endDiff_unique (hd _) Dp _ fun l => by
      rw [(hf _ _).1, Finset.sum_eq_single l]
      · simp
      · intro k _ hk
        simp [Matrix.one_apply_ne hk]
      · simp
  have hmul : ∀ a b, d (a * b) = d a * d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).2, endDiff_spec (hd b), map_sum, map_sum]
      simp only [endDiff_spec (hd a)]
      rw [← map_sum, Finset.sum_comm]
      simp [Matrix.mul_apply, TensorProduct.tmul_sum]
  have hzero : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  exact ⟨⟨⟨⟨d, hone⟩, hmul⟩, hzero, hadd⟩, fun a => hd a⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivLeafGaugeEqPairingAddIntegralStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv C (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  first | exact @GlobalTheory.GaugeDeriv.pderiv_hM | exact GlobalTheory.GaugeDeriv.pderiv_hM | (intros; apply GlobalTheory.GaugeDeriv.pderiv_hM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSemilinearRankNullityModMaxIdealStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  first | exact @GlobalTheory.SemilinearNullity.rank_nullity | exact GlobalTheory.SemilinearNullity.rank_nullity | (intros; apply GlobalTheory.SemilinearNullity.rank_nullity <;> assumption)
end

