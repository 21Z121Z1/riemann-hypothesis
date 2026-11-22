import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionAndIsMonHomOfOpenCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLieCombZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.SquareField
variable {K : Type} [Field K]

def zeroPt (K : Type) [Field K] : 𝟙_ (Over (Sp K)) ⟶ epsR K :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem isTangent_iff {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsTangent v ↔ zeroPt K ≫ v = η[G] := by
  unfold IsTangent
  constructor
  · intro h
    ext1
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun u => u.left) h

theorem isTangent_one {G : Over (Sp K)} [GrpObj G] : IsTangent (1 : epsR K ⟶ G) := by
  rw [isTangent_iff, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt K ≫ toUnit _) (𝟙 _),
    Category.id_comp]

theorem isTangent_lift {G H : Over (Sp K)} [GrpObj G] [GrpObj H] {v : epsR K ⟶ G} {w : epsR K ⟶ H}
    (hv : IsTangent v) (hw : IsTangent w) : IsTangent (lift v w) := by
  rw [isTangent_iff] at hv hw ⊢
  apply CartesianMonoidalCategory.hom_ext
  · simp [hv]
  · simp [hw]

theorem isLieComb_one {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsLieComb (fun _ : Fin 1 => (1 : K)) (fun _ => v) v := by
  refine ⟨fun _ => v, fun _ => ?_, by simp⟩
  simp only [epsScaleR, one_smul, TrivSqZeroExt.map_id]
  simp [spMap]

theorem isLieComb_zero {G : Over (Sp K)} [GrpObj G] :
    IsLieComb (fun _ : Fin 0 => (1 : K)) (fun _ => (1 : epsR K ⟶ G)) 1 := by
  exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem app_eq_pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (h : Γ(Y, W)) :
    (f.app W).hom h = pbT f h (f ⁻¹ᵁ W) := by
  unfold pbT
  rw [dif_pos le_rfl, Scheme.Hom.app_eq_appLE]

theorem constFn_one {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) : constFn q O 1 = 1 := by
  simp [constFn]

private theorem pbT_eq_rsT_pbT_preimage {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀))
    (O : Z.Opens) (hO : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = rsT (pbT f s (f ⁻¹ᵁ O₀)) O := by
  unfold pbT rsT
  rw [dif_pos hO, dif_pos hO, dif_pos (le_refl _), resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem rsT_zero_moduli {Y : Scheme.{0}} {O₀ : Y.Opens} (O : Y.Opens) :
    rsT (0 : Γ(Y, O₀)) O = 0 := by
  unfold rsT
  split <;> simp

section
variable {A₁ A₀ : Over (Sp K)} [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) [IsMonHom f]
  {w : epsR K ⟶ A₁} {dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)}

theorem field_pb {v : epsR K ⟶ A₀} {dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)}
    (hv : IsTangent v) (hd : IsInvDer v dd) (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = v)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = pbT f.left (dd W h) O := by
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 1 (fun _ => v) (fun _ => dd) w dw (fun _ => 1) inferInstance
    (fun _ => hv) hw (fun _ => hd) hdw (by rw [e]; exact isLieComb_one v) W h
  simp only [Fin.sum_univ_one, constFn_one] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, _root_.one_mul, app_eq_pbT,
    ← pbT_eq_rsT_pbT_preimage f.left (dd W h) O hO]

theorem field_pb_zero (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = 1)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = 0 := by
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 0 (fun _ => 1) (fun _ _ x => x) w dw (fun _ => 1) inferInstance
    (fun i => i.elim0) hw (fun i => i.elim0) hdw (by rw [e]; exact isLieComb_zero) W h
  simp only [Fin.sum_univ_zero] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, rsT_zero_moduli]
end

theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), IsTangent v → IsInvDer v dd → ∀ (n n' : A₀ ⊗ A₀ ⟶ A₀), ((n = fst A₀ A₀ ∧ n' = snd A₀ A₀) ∨ (n = snd A₀ A₀ ∧ n' = fst A₀ A₀)) → ∃ dw : ∀ O : (A₀ ⊗ A₀).left.Opens, Γ((A₀ ⊗ A₀).left, O) → Γ((A₀ ⊗ A₀).left, O), (∀ W f f', dw W (f + f') = dw W f + dw W f') ∧ (∀ W f f', dw W (f * f') = f * dw W f' + f' * dw W f) ∧ (∀ W W' (f : Γ((A₀ ⊗ A₀).left, W)), W' ≤ W → dw W' (rsT f W') = rsT (dw W f) W') ∧ (∀ W a, dw W (constFn (A₀ ⊗ A₀).hom W a) = 0) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ (fst A₀ A₀ * snd A₀ A₀).left ⁻¹ᵁ W → dw O (pbT (fst A₀ A₀ * snd A₀ A₀).left h O) = pbT (fst A₀ A₀ * snd A₀ A₀).left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n.left ⁻¹ᵁ W → dw O (pbT n.left h O) = pbT n.left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n'.left ⁻¹ᵁ W → dw O (pbT n'.left h O) = 0) := by
  intro K _ A₀ _ _ v dd hv hd n n' hnn'
  obtain ⟨w, hw, hwn, hwn', hwm⟩ : ∃ w : epsR K ⟶ A₀ ⊗ A₀, IsTangent w ∧ w ≫ n = v ∧ w ≫ n' = 1 ∧
      w ≫ (fst A₀ A₀ * snd A₀ A₀) = v := by
    rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨lift v 1, isTangent_lift hv isTangent_one, lift_fst _ _, lift_snd _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.mul_one]⟩
    · exact ⟨lift 1 v, isTangent_lift isTangent_one hv, lift_snd _ _, lift_fst _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.one_mul]⟩
  have hn : IsMonHom n := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hn' : IsMonHom n' := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hm : IsMonHom (fst A₀ A₀ * snd A₀ A₀) := by
    rw [← MonObj.mul_eq_mul]
    infer_instance
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw).1
  obtain ⟨hadd, hmul, hres, hconst, -⟩ := hprop dw hdw
  refine ⟨dw, hadd, hmul, hres, hconst, ?_, ?_, ?_⟩
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwm W h O hO
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwn W h O hO
  · intro W h O hO
    exact field_pb_zero _ hw hdw hwn' W h O hO

end GlobalTheory.KS.SquareField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubsch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ClosedCoord
open MvPolynomial

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_ideal_factor {Y Z : Scheme.{0}} (i : Y ⟶ Z) [IsClosedImmersion i] {S : Type} [CommRing S]
    (x : Sp S ⟶ Z) : ∃ J : Ideal S, ∀ (R' : Type) [CommRing R'] (φ : S →+* R'),
      (∃ y : Sp R' ⟶ Y, y ≫ i = spMap φ ≫ x) ↔ ∀ f ∈ J, φ f = 0 := by
  obtain ⟨J, e, he⟩ := IsClosedImmersion.Spec_iff.1 (inferInstance : IsClosedImmersion (pullback.snd i x))
  refine ⟨J, fun R' _ φ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩ f hf
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (spMap φ) hy ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ ψ) = spMap φ := by
      rw [Spec.map_comp, hψ, Category.assoc, ← he, pullback.lift_snd]
    have h2 := Spec.map_injective h1
    have h3 : ψ.hom (Ideal.Quotient.mk J f) = φ f := congrArg (fun t => t.hom f) h2
    rw [← h3, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · intro h
    refine ⟨spMap (Ideal.Quotient.lift J φ h) ≫ e.inv ≫ pullback.fst i x, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl

theorem exists_homogenisation {R σ : Type} [CommRing R] (a : σ) (F : MvPolynomial σ R) :
    ∃ (d : ℕ) (G : MvPolynomial σ R),
      (∀ (R' : Type) [CommRing R'] (β : R →+* R') (u : R') (w : σ → R'),
        eval₂ β (fun j => u * w j) G = u ^ d * eval₂ β w G) ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (w : σ → R'), w a = 1 → eval₂ β w G = eval₂ β w F := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, fun _ _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
  | add p q hp hq =>
    obtain ⟨d, G, h1, h2⟩ := hp
    obtain ⟨d', G', h1', h2'⟩ := hq
    refine ⟨d + d', X a ^ d' * G + X a ^ d * G', fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h1, h1']; ring
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h2 _ β w hw, h2' _ β w hw, hw]; ring
  | mul_X p n hp =>
    obtain ⟨d, G, h1, h2⟩ := hp
    refine ⟨d + 1, G * X n, fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_mul, eval₂_X, h1]; ring
    · simp only [eval₂_mul, eval₂_X, h2 _ β w hw]

theorem eq_zero_of_away {R' σ : Type} [CommRing R'] (v : σ → R') (hv : Ideal.span (Set.range v) = ⊤) (r : R')
    (h : ∀ a, algebraMap R' (Localization.Away (v a)) r = 0) : r = 0 := by
  have : r ∈ (⊥ : Ideal R') := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range v) hv r ?_
    rintro ⟨_, a, rfl⟩
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (v a)) _ r).1 (h a)
    exact ⟨n, by simpa using hn⟩
  simpa using this

def awayUnit {R' : Type} [CommRing R'] (r : R') : (Localization.Away r)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).unit

theorem awayUnit_coe {R' : Type} [CommRing R'] (r : R') :
    (awayUnit r : Localization.Away r) = algebraMap R' _ r := rfl

theorem awayUnit_inv_mul {R' : Type} [CommRing R'] (r : R') :
    ((awayUnit r)⁻¹ : (Localization.Away r)ˣ) * algebraMap R' (Localization.Away r) r = 1 := by
  rw [← awayUnit_coe]; exact Units.inv_mul _

theorem away_of_vanishing {R σ : Type} [CommRing R] [Finite σ]
    (P : ∀ (R' : Type) [CommRing R'], (R →+* R') → (σ → R') → Prop)
    (bc : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (φ : R' →+* R'') β v, P R' β v → P R'' (φ.comp β) (fun j => φ (v j)))
    (sc : ∀ (R' : Type) [CommRing R'] (u : R'ˣ) β v, P R' β v → P R' β (fun j => u * v j))
    (uni : ∀ (R' : Type) [CommRing R'] β v, P R' β v → Ideal.span (Set.range v) = ⊤)
    (ch : ∀ a, ∃ K : Ideal (MvPolynomial σ R), X a - 1 ∈ K ∧ ∀ (R' : Type) [CommRing R'] β w, w a = 1 →
      (P R' β w ↔ ∀ F ∈ K, eval₂ β w F = 0))
    (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R')
    (hv : ∀ F, (∀ (R'' : Type) [CommRing R''] β' w, P R'' β' w → eval₂ β' w F = 0) → eval₂ β v F = 0) (a : σ) :
    P (Localization.Away (v a)) ((algebraMap R' _).comp β) (fun j => algebraMap R' _ (v j)) := by
  classical
  choose K hK1 hK using ch
  have := Fintype.ofFinite σ

  have nrm : ∀ (A : Type) [CommRing A] β₀ (t : σ → A) (b : σ), P A β₀ t → ∀ F ∈ K b,
      eval₂ ((algebraMap A (Localization.Away (t b))).comp β₀)
        (fun j => ((awayUnit (t b))⁻¹ : (Localization.Away (t b))ˣ) * algebraMap A _ (t j)) F = 0 := by
    intro A _ β₀ t b ht
    exact (hK b _ _ _ (awayUnit_inv_mul _)).1 (sc _ _ _ _ (bc _ _ _ _ _ ht))
  suffices h : P (Localization.Away (v a)) ((algebraMap R' _).comp β)
      (fun j => ((awayUnit (v a))⁻¹ : (Localization.Away (v a))ˣ) * algebraMap R' _ (v j)) by
    have h2 := sc _ (awayUnit (v a)) _ _ h
    simpa only [Units.mul_inv_cancel_left] using h2
  refine (hK a _ _ _ (awayUnit_inv_mul _)).2 fun F hF => ?_
  obtain ⟨d, G, hG, hGF⟩ := exists_homogenisation a F
  have step : ∀ b, ∃ n : ℕ, X a ^ n * G ∈ K b := by
    intro b
    have hP : P (MvPolynomial σ R ⧸ K b) ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk _ (X j)) := by
      refine (hK b _ _ _ ?_).2 fun F' hF' => ?_
      · rw [← map_one (Ideal.Quotient.mk (K b)), Ideal.Quotient.eq]; exact hK1 b
      · have := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X F').symm
        rw [eval₂_eta, Ideal.Quotient.eq_zero_iff_mem.2 hF'] at this
        exact this
    have h1 := nrm _ _ _ a hP F hF
    rw [← hGF _ _ _ (awayUnit_inv_mul _), hG, (Units.isUnit _).pow d |>.mul_right_eq_zero] at h1
    have h2 := eval₂_comp_left (algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))))
      ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk (K b) (X j)) G
    have h3 := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X G)
    rw [eval₂_eta] at h3
    have h4 : algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))) (Ideal.Quotient.mk (K b) G) = 0 := by
      rw [h3]; exact h2.trans h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk (K b) (X a))) _ _).1 h4
    refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hn
  choose n hn using step
  have hH : eval₂ β v (X a ^ (∑ b, n b) * G) = 0 := by
    refine hv _ fun A _ β₀ t ht => eq_zero_of_away t (uni _ _ _ ht) _ fun b => ?_
    have hm : X a ^ (∑ b, n b) * G ∈ K b := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      rw [hm, pow_add, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hn b)
    have h1 := nrm _ _ _ b ht _ hm
    rw [eval₂_comp_left]
    rw [eval₂_mul, eval₂_pow, eval₂_X, hG, mul_pow, _root_.mul_mul_mul_comm, ← pow_add,
      (Units.isUnit _).pow _ |>.mul_right_eq_zero] at h1
    rw [eval₂_mul, eval₂_pow, eval₂_X]
    exact h1
  have h5 := congrArg (algebraMap R' (Localization.Away (v a))) hH
  rw [eval₂_mul, eval₂_pow, eval₂_X, map_mul, map_pow, map_zero, ← awayUnit_coe,
    (Units.isUnit _).pow _ |>.mul_right_eq_zero, eval₂_comp_left] at h5
  rw [← hGF _ _ _ (awayUnit_inv_mul _), hG]
  exact mul_eq_zero_of_right _ h5

theorem projRep_closed : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : Y ⟶ Z) (N : LB Y) (ty : σ → N.Sec), ProjRep I s M th → IsClosedImmersion i → N.IsLB → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ i) v) → ProjRep (idealOf (i ≫ s) N ty (𝟙 Y)) (i ≫ s) N ty := by
  intro R σ _ _ I Z Y s M th i N ty ⟨hM, hloc, hpts⟩ hi hN hc
  have mem : ∀ F, F ∈ idealOf (i ≫ s) N ty (𝟙 Y) ↔ ∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y)
      (v : σ → R'), y ≫ i ≫ s = spMap β → SecCoord M th (y ≫ i) v → eval₂ β v F = 0 := by
    intro F
    simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, coe_eval₂Hom, Category.comp_id, hc, and_imp]
  have hbc : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Sp A ⟶ Z) (v : σ → A),
      SecCoord M th x v → SecCoord M th (spMap φ ≫ x) (fun j => φ (v j)) :=
    fun A B _ _ φ x v h => (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th A x v hM h).1 B φ
  have huniq : ∀ (A : Type) [CommRing A] (β : R →+* A) (v : σ → A) (x x' : Sp A ⟶ Z), x ≫ s = spMap β →
      SecCoord M th x v → x' ≫ s = spMap β → SecCoord M th x' v → x = x' := by
    intro A _ β v x x' h1 h2 h3 h4
    obtain ⟨h5, h6⟩ := hloc A β x v h1 h2
    exact (hpts A β v h5 h6).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  refine ⟨hN, fun R' _ β y v h1 h2 => ?_, fun R' _ β v hv hI => ?_⟩
  · rw [hc] at h2
    exact ⟨(hloc R' β (y ≫ i) v (by simpa using h1) h2).1, fun F hF => (mem F).1 hF R' β y v h1 h2⟩
  have hIv : ∀ F ∈ I, eval₂ β v F = 0 := fun F hF => hI F ((mem F).2 fun A _ β' y w h1 h2 =>
    (hloc A β' (y ≫ i) w (by simpa using h1) h2).2 F hF)
  obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hpts R' β v hv hIv
  have key := away_of_vanishing (R := R) (σ := σ)
    (fun A _ β' w => ∃ y : Sp A ⟶ Y, y ≫ i ≫ s = spMap β' ∧ SecCoord M th (y ≫ i) w)
    (by
      rintro A B _ _ φ β' w ⟨y, h1, h2⟩
      refine ⟨spMap φ ≫ y, by rw [Category.assoc, h1, spMap_comp_eq], ?_⟩
      rw [Category.assoc]; exact hbc _ _ φ _ _ h2)
    (by
      rintro A _ u β' w ⟨y, h1, h2⟩
      exact ⟨y, h1, (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th A _ w hM h2).2.1 u⟩)
    (by
      rintro A _ β' w ⟨y, h1, h2⟩
      exact (hloc A β' (y ≫ i) w (by simpa using h1) h2).1)
    (by
      intro a
      have hq : ∀ F, eval₂ ((Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})).comp C)
          (fun j => Ideal.Quotient.mk _ (X j)) F = Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1}) F := by
        intro F
        have := (eval₂_comp_left (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})) C X F).symm
        rw [eval₂_eta] at this
        exact this
      have ha : X a - 1 ∈ I ⊔ Ideal.span {X a - 1} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      obtain ⟨xa, ⟨hxa1, hxa2⟩, -⟩ := hpts (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {X a - 1}))
        ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk _ (X j))
        (by
          rw [Ideal.eq_top_iff_one]
          refine Ideal.subset_span ⟨a, ?_⟩
          rw [← map_one (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1}))]
          exact Ideal.Quotient.eq.2 ha)
        (fun F hF => by rw [hq]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))
      obtain ⟨J, hJ⟩ := exists_ideal_factor i xa
      have hle : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, F ∈ J.comap (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})) := by
        intro F hF
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hF]; exact J.zero_mem
      refine ⟨J.comap (Ideal.Quotient.mk _), hle _ ha, fun A _ β' w hw => ?_⟩
      have main : ∀ h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0,
          (spMap (Ideal.Quotient.lift _ _ h) ≫ xa) ≫ s = spMap β' ∧
            SecCoord M th (spMap (Ideal.Quotient.lift _ _ h) ≫ xa) w := by
        intro h
        refine ⟨?_, ?_⟩
        · rw [Category.assoc, hxa1, spMap_comp_eq]
          congr 1
          ext r
          simp
        · have := hbc _ _ (Ideal.Quotient.lift _ _ h) _ _ hxa2
          simpa using this
      constructor
      · rintro ⟨y, h1, h2⟩ F hF
        have h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0 := by
          intro F hF
          have hle' : I ⊔ Ideal.span {X a - 1} ≤ RingHom.ker (eval₂Hom β' w) := by
            refine sup_le (fun F hF => (hloc A β' (y ≫ i) w (by simpa using h1) h2).2 F hF) ?_
            rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
            simp [hw]
          exact hle' hF
        have e := huniq A β' w _ _ (by simpa using h1) h2 (main h).1 (main h).2
        exact (hJ A _).1 ⟨y, e⟩ _ hF
      · intro hF
        have h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0 := fun F h => hF F (hle F h)
        obtain ⟨y, hy⟩ := (hJ A (Ideal.Quotient.lift _ _ h)).2 (by
          intro f hf
          obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
          exact hF F hf)
        exact ⟨y, by rw [← Category.assoc, hy]; exact (main h).1, by rw [hy]; exact (main h).2⟩)
    R' β v (fun F hF => hI F ((mem F).2 fun A _ β' y w h1 h2 => hF A β' w ⟨y, h1, h2⟩))
  obtain ⟨J, hJ⟩ := exists_ideal_factor i x
  obtain ⟨y, hy⟩ := (hJ R' (RingHom.id R')).2 (by
    intro f hf
    refine eq_zero_of_away v hv f fun a => ?_
    obtain ⟨y, h1, h2⟩ := key a
    refine (hJ _ (algebraMap R' _)).1 ⟨y, ?_⟩ f hf
    refine huniq _ _ _ _ _ (by simpa using h1) h2 ?_ (hbc _ _ _ _ _ hx2)
    rw [Category.assoc, hx1, spMap_comp_eq])
  have hid : spMap (RingHom.id R') = 𝟙 (Sp R') := Spec.map_id _
  rw [hid, Category.id_comp] at hy
  refine ⟨y, ⟨by rw [← Category.assoc, hy, hx1], by rw [hc, hy]; exact hx2⟩, ?_⟩
  rintro y' ⟨h1, h2⟩
  rw [hc] at h2
  rw [← cancel_mono i, hy]
  exact huniq _ _ _ _ _ (by simpa using h1) h2 hx1 hx2

end GlobalTheory.ZM.ClosedCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R')
    (w : σ → R') (u : σ →₀ ℕ) (a : R) :
    MvPolynomial.eval₂ ((Polynomial.C : R' →+* Polynomial R').comp β) (fun i => Polynomial.X * Polynomial.C (w i))
        (MvPolynomial.monomial u a) =
      Polynomial.C (MvPolynomial.eval₂ β w (MvPolynomial.monomial u a)) * Polynomial.X ^ u.degree := by
  simp only [MvPolynomial.eval₂_monomial, RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Polynomial.C_pow, ← map_prod, map_mul, Finsupp.degree_apply]
  ring

theorem coeff_eval₂_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  refine MvPolynomial.induction_on' F (fun u a => ?_) (fun p q hp hq => ?_)
  · simp only [MvPolynomial.coe_eval₂Hom]
    rw [eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_monomial a rfl))]
    split_ifs <;> simp
  · simp only [map_add, Polynomial.coeff_add, hp, hq]

theorem eval₂_homogeneousComponent_eq_zero {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ)
    (h : MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_eval₂_scale β w F e]
  have key : Polynomial.toLaurent (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F) =
      MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
        (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F := by
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext r
      simp
    · funext i
      simp
  rw [h, ← map_zero Polynomial.toLaurent] at key
  rw [Polynomial.toLaurent_injective key, Polynomial.coeff_zero]

theorem spMap_comp_ringHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (β : A →+* B) (φ : B →+* C) :
    spMap φ ≫ spMap β = spMap (φ.comp β) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

private theorem secCoord_laurent_T_mul_C_of_secCoord {X Y : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {R' : Type}
    [CommRing R'] (y : Sp R' ⟶ Y) (a : Y ⟶ X) (v : σ → R') (h : SecCoord M th (y ≫ a) v) :
    SecCoord M th ((spMap (LaurentPolynomial.C : R' →+* LaurentPolynomial R') ≫ y) ≫ a)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i)) := by
  let u : (LaurentPolynomial R')ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  rw [Category.assoc]
  exact Coord.scale (Coord.baseChange h LaurentPolynomial.C) u

theorem ideals_homogeneous : (∀ (R σ : Type) [CommRing R] (Y X : Scheme.{0}) (s : Y ⟶ Sp R) (M : LB X) (th : σ → M.Sec) (a : Y ⟶ X), M.IsLB → (∀ F ∈ idealOf s M th a, ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf s M th a)) ∧ (∀ (R σ₁ σ₂ : Type) [CommRing R] (Y X₁ X₂ : Scheme.{0}) (s : Y ⟶ Sp R) (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂), M₁.IsLB → M₂.IsLB → (∀ F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂, ∀ e, MvPolynomial.homogeneousComponent e F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂)) ∧ ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → ProjRep (idealOf s M th (𝟙 Z)) s M th := by
  refine ⟨?_, ?_, ?_⟩
  · intro R σ _ Y X s M th a _ F hF e
    simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a v hyv.2⟩
    exact eval₂_homogeneousComponent_eq_zero β v F e h0
  · intro R σ₁ σ₂ _ Y X₁ X₂ s M₁ th₁ a₁ M₂ th₂ a₂ _ _ F hF e
    simp only [graphIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v₁ v₂ hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i))
      (fun i => LaurentPolynomial.C (v₂ i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a₁ v₁ hyv.2.1,
        by rw [Category.assoc]; exact Coord.baseChange hyv.2.2 LaurentPolynomial.C⟩
    have hfun : (fun i : σ₁ × σ₂ => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1 * v₂ i.2)) =
        fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1) * LaurentPolynomial.C (v₂ i.2) := by
      funext i
      rw [map_mul, ← _root_.mul_assoc]
    exact eval₂_homogeneousComponent_eq_zero β (fun i : σ₁ × σ₂ => v₁ i.1 * v₂ i.2) F e
      ((congrArg (fun g => MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp β) g F) hfun).trans h0)
  · intro R σ _ I Z s M th hI
    have hle : ∀ F ∈ I, F ∈ idealOf s M th (𝟙 Z) := by
      intro F hF
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker]
      intro R' _ β y v hyv
      rw [Category.comp_id] at hyv
      exact (hI.2.1 R' β y v hyv.1 hyv.2).2 F hF
    refine ⟨hI.1, ?_, ?_⟩
    · intro R' _ β x v hx hc
      refine ⟨(hI.2.1 R' β x v hx hc).1, fun F hF => ?_⟩
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF
      exact hF R' inferInstance β x v ⟨hx, by rwa [Category.comp_id]⟩
    · intro R' _ β v hv hz
      exact hI.2.2 R' β v hv fun F hF => hz F (hle F hF)

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionAndIsMonHomOfOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_and_isMonHom_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ (k : ℕ) (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, x' i ^ k = 1) → x ^ k = 1) ∧ ∀ (f : A ⟶ A) (f' : ∀ i, G i ⟶ G i), (∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) → (∀ i, IsMonHom (f' i)) → IsMonHom f := by
  first | exact @GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover | exact GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover | (intros; apply GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover <;> assumption)
end

