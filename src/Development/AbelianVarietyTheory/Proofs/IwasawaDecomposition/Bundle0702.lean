import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullFlagFamilyLieCompatibleGraded
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlagTie

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

def Lower (g : Mat m K) : Prop := ∀ τ (i k : Fin (m τ)), i < k → g τ i k = 0

theorem lower_iff_blockTriangular (g : Mat m K) (τ : ι) :
    (∀ i k : Fin (m τ), i < k → g τ i k = 0) ↔ (g τ).BlockTriangular OrderDual.toDual :=
  ⟨fun h _ _ hik => h _ _ hik, fun h _ _ hik => h hik⟩

theorem Lower.mul {g h : Mat m K} (hg : Lower g) (hh : Lower h) : Lower (g * h) := fun τ =>
  (lower_iff_blockTriangular (g * h) τ).2
    (((lower_iff_blockTriangular g τ).1 (hg τ)).mul ((lower_iff_blockTriangular h τ).1 (hh τ)))

theorem Lower.inv {g : Mat m K} (hg : Lower g) : Lower g⁻¹ := fun τ => by
  by_cases hd : (g τ).det = 0
  · intro i k _
    show (g τ)⁻¹ i k = 0
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hd])]
    rfl
  · have := (g τ).invertibleOfIsUnitDet (Ne.isUnit hd)
    exact (lower_iff_blockTriangular g⁻¹ τ).2
      (Matrix.blockTriangular_inv_of_blockTriangular ((lower_iff_blockTriangular g τ).1 (hg τ)))

theorem Lower.det_eq {g : Mat m K} (hg : Lower g) (τ : ι) : (g τ).det = ∏ i, g τ i i :=
  Matrix.det_of_lowerTriangular _ ((lower_iff_blockTriangular g τ).1 (hg τ))

theorem lower_one : Lower (1 : Mat m K) := fun _ _ _ hik => Matrix.one_apply_ne hik.ne

theorem par_full_iff {O : Subring K} {g : Mat m K} : Par m O g ↔ Par 0 O g ∧ Lower g := by
  constructor
  · intro h
    exact ⟨h.mono (fun _ => Nat.zero_le _) le_rfl, fun τ i k hik => (h τ).2.2.2 i k i.2 hik⟩
  · rintro ⟨h, hl⟩ τ
    exact ⟨(h τ).1, (h τ).2.1, (h τ).2.2.1, fun i k _ hik => hl τ i k hik⟩

theorem lower_mul_iff {B L : Mat m K} (hl : Lower L) (hL : ∀ τ, (L τ).det ≠ 0) : Lower (B * L) ↔ Lower B := by
  refine ⟨fun h => ?_, fun h => h.mul hl⟩
  have := h.mul hl.inv
  rwa [mul_assoc, Mat.mul_inv hL, mul_one] at this

end Tri

section Nhds

variable {F : Type} [Field F] {ι : Type} [Finite ι] {m : ι → ℕ}

theorem mem_O_generic (Y : Var F) (x : Y.Fn) : x ∈ ((ratOf Y).O (genericPoint Y.X)).toSubring :=
  (mem_O_ratOf (Y := Y) (y := genericPoint Y.X) (g := x)).2 ⟨x, by
    show (Y.X.presheaf.stalkSpecializes _).hom x = x
    rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl⟩

theorem eventually_mem_O {Y : Var F} {z : Y.X} {g : Y.Fn} (h : g ∈ ((ratOf Y).O z).toSubring) :
    ∀ᶠ z' in nhds z, g ∈ ((ratOf Y).O z').toSubring := by
  obtain ⟨U, hz, a, rfl⟩ := (mem_O_ratOf.1 h).exists_fnOf
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hz) fun z' hz' => mem_O_ratOf.2 (regAt_fnOf hz' _ a)

theorem eventually_par {Y : Var F} {z : Y.X} {g : Mat m Y.Fn} (h : Par 0 ((ratOf Y).O z).toSubring g) :
    ∀ᶠ z' in nhds z, Par 0 ((ratOf Y).O z').toSubring g := by
  have h1 : ∀ᶠ z' in nhds z, ∀ τ i j, g τ i j ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_mem_O ((h τ).1 i j)
  have h2 : ∀ᶠ z' in nhds z, ∀ τ, (g τ).det⁻¹ ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => eventually_mem_O (h τ).2.2.1
  filter_upwards [h1, h2] with z' h1 h2 τ
  exact ⟨h1 τ, (h τ).2.1, h2 τ, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩

end Nhds

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

abbrev base (C : FlagCpt Z e) : Fr (ratOf C.Y) Dw.mult 0 := TieBase.fam e C.Y C.π C.π_str C.f0

theorem exists_lower (C : FlagCpt Z e) (y : C.Y.X) :
    ∃ (L : Mat Dw.mult C.Y.Fn) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      L⁻¹ ∈ (base C).S y ∧ (∀ τ, (L τ).det ≠ 0) ∧ Lower L ∧ (∀ τ i, L τ i i = t τ i) ∧
        ∀ τ i, (C.gr τ i).IsEqn y (t τ i) := by
  obtain ⟨φ, f, t, htri, hgr⟩ := C.gr_spec y
  obtain ⟨L, hc, hd, hl⟩ := (EigFrame.tri_iff f _ C.f0 t).1 htri
  have hL : ∀ τ, (L τ).det ≠ 0 := fun τ => by
    rw [Lower.det_eq hl τ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [hd]; exact (t τ i).ne_zero
  refine ⟨L, t, ?_, hL, hl, hd, hgr⟩
  show (∀ τ, (L⁻¹ τ).det ≠ 0) ∧ _
  refine ⟨fun τ => (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hL) τ)).ne_zero, φ, f, ?_⟩
  rw [Mat.inv_inv hL]
  exact hc

theorem one_mem_base (C : FlagCpt Z e) : (1 : Mat Dw.mult C.Y.Fn) ∈ (base C).S (genericPoint C.Y.X) := by
  obtain ⟨A, hA⟩ := (base C).nonempty (genericPoint C.Y.X)
  refine (Fr.mem_iff hA).2 fun τ => ?_
  refine ⟨fun _ _ => mem_O_generic _ _, ?_, mem_O_generic _ _, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [one_mul]
  exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul (Fr.det_ne hA)) τ)).ne_zero

def flagFam (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn) (hA₁ : ∀ τ, (A₁ τ).det ≠ 0) : Fr (ratOf C.Y) Dw.mult Dw.mult where
  S y := {A' | A' * A₁⁻¹ ∈ (base C).S y ∧ Lower (A' * A₁⁻¹)}
  loc z := by
    obtain ⟨L, -, hLS, hL, hl, -, -⟩ := exists_lower C z
    obtain ⟨U₀, T, hz, -, hU₀⟩ := (base C).loc z
    have hev : ∀ᶠ z' in nhds z, L⁻¹ ∈ (base C).S z' :=
      (Filter.eventually_and.2 ⟨Filter.eventually_of_mem (U₀.isOpen.mem_nhds hz) fun _ h => h,
        eventually_par ((hU₀ z hz L⁻¹).1 hLS)⟩).mono fun z' h => (hU₀ z' h.1 L⁻¹).2 h.2
    obtain ⟨W, hW, hWo, hzW⟩ := eventually_nhds_iff.1 hev
    refine ⟨⟨W, hWo⟩, L⁻¹ * A₁, hzW, fun τ => ?_, fun z' hz' A' => ?_⟩
    · rw [Pi.mul_apply, Matrix.det_mul]
      exact mul_ne_zero (Fr.det_ne hLS τ) (hA₁ τ)
    · have hz'' : L⁻¹ ∈ (base C).S z' := hW z' hz'
      show (A' * A₁⁻¹ ∈ (base C).S z' ∧ Lower (A' * A₁⁻¹)) ↔ _
      rw [Fr.mem_iff hz'', Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, par_full_iff, lower_mul_iff hl hL]

theorem exists_tied_isGraded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type)
    [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn), (∀ τ, (A₁ τ).det ≠ 0) →
    ∃ E' : Fr (ratOf C.Y) Dw.mult Dw.mult, Tied e C.Y C.π C.f0 E' A₁ ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C A₁ hA₁
  have hA : A₁ ∈ (flagFam C A₁ hA₁).S (genericPoint C.Y.X) := by
    show A₁ * A₁⁻¹ ∈ (base C).S _ ∧ Lower (A₁ * A₁⁻¹)
    rw [Mat.mul_inv hA₁]
    exact ⟨one_mem_base C, lower_one⟩
  refine ⟨flagFam C A₁ hA₁, ⟨hA, fun y A h => ?_⟩, ⟨A₁, hA, fun y x => ?_⟩⟩
  · obtain ⟨-, φ, f, hf⟩ := h.1
    rw [Mat.mul_inv_rev, Mat.inv_inv hA₁] at hf
    exact ⟨φ, f, hf⟩
  · obtain ⟨L, t, hLS, hL, hl, hd, hgr⟩ := exists_lower C y
    refine ⟨L⁻¹ * A₁, ?_, t x.1 x.2, ?_, hgr x.1 x.2⟩
    · show L⁻¹ * A₁ * A₁⁻¹ ∈ (base C).S y ∧ Lower (L⁻¹ * A₁ * A₁⁻¹)
      rw [mul_assoc, Mat.mul_inv hA₁, mul_one]
      exact ⟨hLS, hl.inv⟩
    · rw [Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, Mat.mul_inv hA₁, one_mul]
      exact hd _ _

end Main

end GlobalTheory.ShFam.FlagTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFrameTranscendentalSpecialisingTwo
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFrame

open Matrix ReciprocityTheory.ChartRestriction.G.PullbackSections

def mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) R := (1 - u) • (1 : Matrix (Fin n) (Fin n) R) + u • A.map κ

theorem mixM_map {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {n : ℕ} (κ : K →+* R) (u : R)
    (A : Matrix (Fin n) (Fin n) K) (ψ : R →+* R') : (mixM κ u A).map ψ = mixM (ψ.comp κ) (ψ u) A := by
  ext a b
  by_cases h : a = b
  · subst h; simp [mixM]
  · simp [mixM, Matrix.one_apply_ne h]

def detPoly {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Polynomial K :=
  (mixM Polynomial.C Polynomial.X A).det

theorem det_mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    (mixM κ u A).det = (detPoly A).eval₂ κ u := by
  rw [detPoly, ← Polynomial.coe_eval₂RingHom, RingHom.map_det, RingHom.mapMatrix_apply, mixM_map]
  congr 2
  · ext a; simp
  · simp

theorem mixM_zero {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 0 A = 1 := by
  simp [mixM]

theorem mixM_one {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 1 A = A := by
  simp [mixM]

theorem detPoly_ne_zero {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : detPoly A ≠ 0 := by
  intro h
  have := det_mixM (RingHom.id K) 0 A
  rw [h, mixM_zero, Polynomial.eval₂_zero, det_one] at this
  exact one_ne_zero this

end GlobalTheory.GenFrame

namespace GlobalTheory.GenFrame

open Matrix Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions GlobalTheory.CxPts GlobalTheory.LieMet

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_co_eq {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (hT : ∀ τ, IsUnit (T τ).det) :
    ∃ g : EigFrame Z φ x, ∀ τ, f.co g τ = T τ := by
  have hsum : ∀ τ (a : Fin (Dw.mult τ) → R),
      ∑ i, a i • ∑ j, T τ j i • f.vec τ j = ∑ j, (T τ *ᵥ a) j • f.vec τ j := by
    intro τ a
    simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  let g : EigFrame Z φ x := EigFrame.ofVec (fun τ i => ∑ j, T τ j i • f.vec τ j)
    (fun τ i a => by
      simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _)
    (fun τ w hw => by
      obtain ⟨b, hb, hbu⟩ := f.existsUnique_sum τ w hw
      refine ⟨(T τ)⁻¹ *ᵥ b, ?_, fun a ha => ?_⟩
      · show w = ∑ i, ((T τ)⁻¹ *ᵥ b) i • ∑ j, T τ j i • f.vec τ j
        rw [hsum, mulVec_mulVec, mul_nonsing_inv _ (hT τ), one_mulVec]
        exact hb
      · have h1 : T τ *ᵥ a = b := hbu _ (ha.trans (hsum τ a))
        rw [← h1, mulVec_mulVec, nonsing_inv_mul _ (hT τ), one_mulVec])
  refine ⟨g, fun τ => EigFrame.co_eq fun i => ?_⟩
  exact (isComb_iff (f.vec τ) (fun a => T τ a i) (∑ j, T τ j i • f.vec τ j)).2 rfl

theorem co_eq_one {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f₀ f₁ f₂ : EigFrame Z φ x}
    {τ : E →+* ℂ} (h : f₀.co f₁ τ = f₀.co f₂ τ) : f₁.co f₂ τ = 1 := by
  rw [← f₁.co_mul f₀ f₂ τ, ← h, f₁.co_mul f₀ f₁ τ, f₁.co_self τ]

theorem tri_of_co_eq_one {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'}
    (hf : f.IsMap ψ f') (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) (h : ∀ τ, f'.co g τ = 1) : f.Tri ψ g 1 := by
  refine ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, by simp [h], fun k hk => by
    simp [h, Matrix.one_apply_ne hk.ne'], ?_⟩⟩
  rw [← funext (hf τ)]
  exact f'.co_spec g τ i

theorem isMap_id {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) :
    f.IsMap (RingHom.id R) f := fun τ i => by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  rw [h1, Category.id_comp]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenFrame

open Matrix in

theorem GlobalTheory.GenFrame.exists_generic_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x) (L : Type) [Field L] (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) → ∀ (xL : Sp L ⟶ Z.X), xL = spMap ι ≫ x → ∃ gL : EigFrame Z (ι.comp χ) xL, ∀ (V : Type) [CommRing V] [IsLocalRing V] (ν : V →+* L) (ιV : K →+* V) (r : V →+* K) (sV : V), ν.comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V → ν sV = s → (r sV = 0 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g tk) ∧ (r sV = 1 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g' tk) := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ χ x g g' L _ ι s hs xL hxL
  have hP : ∀ τ, (GlobalTheory.GenFrame.detPoly (g.co g' τ)).eval₂ ι s ≠ 0 := fun τ h =>
    GlobalTheory.GenFrame.detPoly_ne_zero _ (hs _ h)
  obtain ⟨gB, hgB⟩ := g.exists_isMap ι (φ' := ι.comp χ) rfl hxL
  obtain ⟨gL, hgL⟩ := GlobalTheory.GenFrame.exists_co_eq gB (fun τ => GlobalTheory.GenFrame.mixM ι s (g.co g' τ)) fun τ => by
    rw [GlobalTheory.GenFrame.det_mixM]
    exact (hP τ).isUnit
  refine ⟨gL, fun V _ _ ν ιV r sV hνι hrι hker hνs => ?_⟩
  obtain ⟨gVB, hgVB⟩ := g.exists_isMap ιV (φ' := ιV.comp χ) (x' := spMap ιV ≫ x) rfl rfl
  have hxν : xL = spMap ν ≫ spMap ιV ≫ x := by
    rw [hxL, ← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hνι]
  have hxr : x = spMap r ≫ spMap ιV ≫ x := by
    rw [← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hrι]
    exact (Category.id_comp x).symm.trans (congrArg (· ≫ x) (Spec.map_id _).symm)
  have hφν : ι.comp χ = ν.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hνι]
  have hφr : χ = r.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hrι]; rfl
  have hBν : gVB.IsMap ν gB := fun τ i => by
    rw [hgB τ i, hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hνι]
  have hBr : gVB.IsMap r g := fun τ i => by
    rw [hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hrι]
    exact (GlobalTheory.GenFrame.isMap_id g τ i)

  have main : ∀ (hu : ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det),
      ∃ gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x), gV.Tri ν gL 1 ∧
        ∃ gVr : EigFrame Z χ x, gV.IsMap r gVr ∧ ∀ τ, g.co gVr τ = GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ) := by
    intro hu
    obtain ⟨gV, hgV⟩ := GlobalTheory.GenFrame.exists_co_eq gVB (fun τ => GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)) hu
    obtain ⟨gVν, hgVν⟩ := gV.exists_isMap ν hφν hxν
    obtain ⟨gVr, hgVr⟩ := gV.exists_isMap r hφr hxr
    refine ⟨gV, GlobalTheory.GenFrame.tri_of_co_eq_one hgVν hφν hxν fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := gB) ?_, gVr, hgVr,
      fun τ => ?_⟩
    · rw [hBν.co τ hgVν hxν, hgV, hgL, GlobalTheory.GenFrame.mixM_map, hνι, hνs]
    · rw [hBr.co τ hgVr hxr, hgV, GlobalTheory.GenFrame.mixM_map, hrι]
  have hunit : (∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det ≠ 0) →
      ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det := fun h τ => by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hker, RingHom.mem_ker]
    exact h τ
  have hr : ∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det =
      (GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ)).det := fun τ => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.GenFrame.mixM_map, hrι]
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h0, GlobalTheory.GenFrame.mixM_zero, det_one]; exact one_ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h0, GlobalTheory.GenFrame.mixM_zero, g.co_self]
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h1, GlobalTheory.GenFrame.mixM_one]; exact (g.isUnit_det_co g' τ).ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h1, GlobalTheory.GenFrame.mixM_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_of_inRCone_cell {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (hlin : φ.LinearOn G) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (G i) : ℝ) = N * φ.evalZ (G i))
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone G β) : (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff φ G).1 hlin c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring

theorem inRCone_of_nat_rel {X : Type} [AddCommGroup X] {n : ℕ} {δ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin n → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • δ i) : InRCone δ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * δ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * (β a b : ℝ) = ∑ i, (c i : ℝ) * (δ i a b : ℝ) := by exact_mod_cast h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ i, (c i : ℝ) * (δ i a b : ℝ)) / k from by rw [← h2]; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_cut_of_cell_le : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ,
      (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := by
  intro O _ bar φ X _ _ _ m n G δ hG hδ hin
  obtain ⟨NG, ℓG, hNG, g1, -, -⟩ := hG.strict
  obtain ⟨Nδ, ℓδ, hNδ, d1, d2, d3⟩ := hδ.strict
  have hNG' : (0 : ℝ) < NG := by exact_mod_cast hNG
  have key : ∀ β : LinearMap.BilinForm ℤ X, InRCone G β → (ℓG β : ℝ) = NG * φ.evalZ β :=
    fun β hβ => apply_eq_of_inRCone_cell hG.linear g1 hβ
  have hval : ∀ β : LinearMap.BilinForm ℤ X, (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) β : ℤ)) : ℝ) = NG * ℓδ β - Nδ * ℓG β :=
    fun β => by simp
  refine ⟨(NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG, fun j => ?_, fun k => ?_, fun β hβ hp hc h0 => ?_⟩
  · have h1 : (0 : ℝ) ≤ (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (G j) : ℤ)) : ℝ) := by
      rw [hval, g1 j]
      have := d2 (G j) (hG.mem j) (hG.nonneg j)
      nlinarith
    exact_mod_cast h1
  · have h1 : (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (δ k) : ℤ)) : ℝ) = 0 := by
      rw [hval, key _ (hin k), d1 k]; ring
    exact_mod_cast h1
  · have h1 := hval β
    rw [h0, key β hc] at h1
    have h2 : (Nδ : ℝ) * φ.evalZ β = ℓδ β := by
      have : (NG : ℝ) * ((Nδ : ℝ) * φ.evalZ β - ℓδ β) = 0 := by push_cast at h1; linarith
      have := (mul_eq_zero.1 this).resolve_left hNG'.ne'
      linarith
    obtain ⟨k, c, hk, e⟩ := d3 β hβ hp h2
    exact inRCone_of_nat_rel hk e

example : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X), IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := exists_cut_of_cell_le

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsEOfHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isE_of_heq {𝒮 : Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit 𝒮 K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt 𝒮 K, q.Is D O ∧ EntC q.x.ker := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx⟩

theorem exists_isE_pt {𝒮 : Slots} (H : WitMv 𝒮) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {O : Obj2 (w.D Z)} (x : Wit 𝒮 K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact exists_isE_of_heq (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy

theorem witExE_of_witMv : ∀ 𝒮 : Slots, WitMv 𝒮 → WitExE 𝒮 := fun 𝒮 H _ β hβ =>
  positionOf_ind (P := GoodE 𝒮) (R := fun K X _ _ c => ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker)
    (fun _ _ _ _ _ _ _ g => g.1.elim fun b hb => exists_isE_pt H (b.wit g.2) hb) hβ β.Y β.hY β.p

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelWithRatioStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_with_ratio : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → N2 Y → ∀ (Z : Mdl Y i₀) st (x : Letter Dw), letterOf Dw st = some x → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → HasRatio Z st → ∃ (Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ IsMap Z' Z f ∧ HasPRatio Z' st := by
  first | exact @GlobalTheory.HTLine.exists_pRatio | exact GlobalTheory.HTLine.exists_pRatio | (intros; apply GlobalTheory.HTLine.exists_pRatio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.TraitUnif

theorem exists_ext_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (t' : SAB H (Sp W')) (_ : SABMap t' Y.t (spMap ι ≫ χ)) (_ : PELUnif (maximalIdeal W') t'), CDvr W' ∧ Function.Injective ι ∧ IsLocalHom ι := by
  intro E _ _ _ H D l Xo c Y W _ _ _ hW χ hgen
  obtain ⟨hdvr, hc, hz⟩ := hW
  have hid : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have hj : IsOpenImmersion Y.j := by
    have := Y.jQ_open
    unfold Model.j
    infer_instance
  let x₀ : Sp (FractionRing W) ⟶ Xo.XF c := IsOpenImmersion.lift Y.j (jK W ≫ χ) hgen
  have hx₀ : x₀ ≫ Y.j = jK W ≫ χ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨PP, cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull χ Y.t
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull x₀ Y.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m n₁
  have hx₀' : x₀ ≫ Y.jQ ≫ pullback.fst _ _ = jK W ≫ χ := hx₀
  rw [hx₀'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap n₁
  let T : Formalism.L2.Pj.CDVR := @Formalism.L2.Pj.CDVR.mk W _ _ hdvr hc hz
  obtain ⟨T', φ, t', m', hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T _ _ mK _ mx
  obtain ⟨m'', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have hloc : IsLocalHom φ := RingHom.IsIntegral.isLocalHom hf.to_isIntegral hi
  exact ⟨T'.V, inferInstance, inferInstance, inferInstance, φ, t', m'', P, ⟨inferInstance, inferInstance, inferInstance⟩, hi, hloc⟩

end GlobalTheory.TraitUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  first | exact @GlobalTheory.UnifCoordPull.exists_unif_psiCoord | exact GlobalTheory.UnifCoordPull.exists_unif_psiCoord | (intros; apply GlobalTheory.UnifCoordPull.exists_unif_psiCoord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellValuativeExistenceOverUnionOfOpensStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_valuativeExistence_over_union_of_opens : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  first | exact @GlobalTheory.FlagEmb.Valu.exists_integral_cell | exact GlobalTheory.FlagEmb.Valu.exists_integral_cell | (intros; apply GlobalTheory.FlagEmb.Valu.exists_integral_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHoldStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDR_of_allSteps_hold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z Z' : Mdl Y i₀), (∀ σ, Z'.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ t ∈ allSteps (Lat.top Z), Step.Holds t Z') → HasDR Z' := by
  first | exact @GlobalTheory.LocM.StepFrame.hasDR_of_allSteps | exact GlobalTheory.LocM.StepFrame.hasDR_of_allSteps | (intros; apply GlobalTheory.LocM.StepFrame.hasDR_of_allSteps <;> assumption)
end

