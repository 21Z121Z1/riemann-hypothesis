import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frMapUniq_scal_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x (1 : S) i = 1 := by
  unfold scal ReciprocityTheory.ChartRestriction.G.Out.liftFun
  simp only [map_one]

theorem frMapUniq_chart_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
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

theorem frMapUniq_refl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 _ := Spec.map_id _
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    have hd : dualMap (RingHom.id S) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    show spMap (dualMap (RingHom.id S)) = _
    rw [hd]
    exact Spec.map_id _
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _, by simp,
    by rw [eid]; simp, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem frMap_unique_refl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  refine ⟨?_, frMapUniq_refl y, fun z => ?_⟩
  · rintro ⟨x, xo, u, t, e, b, s, g⟩ ⟨x', xo', u', t', e', b', s', g'⟩ ⟨hx, hu, pm, hs, hf, ha⟩
      ⟨hx', hu', pm', hs', hf', ha'⟩
    dsimp only at hx hu hx' hu' pm pm' hs hf ha hs' hf' ha'
    have h1 : x = x' := hx.trans hx'.symm
    subst h1
    have h2 : u = u' := by
      funext τ i
      exact (hu τ i).trans (hu' τ i).symm
    subst h2
    have h3 : pm = pm' := by
      apply pullback.hom_ext
      · exact hf.trans hf'.symm
      · exact hs.trans hs'.symm
    subst h3
    have h4 : s = s' := by
      have : s.f = s'.f := by
        funext i
        have h := frMapUniq_chart_le pm hs i
        exact (ha i h).symm.trans (ha' i h)
      cases s; cases s'
      congr
    subst h4
    rfl
  · have k : ∀ i : (PPx y.x).ι, scal y.x (1 : S) i * y.s.f i = y.s.f i := fun i => by
      rw [frMapUniq_scal_one, _root_.one_mul]
    constructor
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).trans (ha i h)⟩
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).symm.trans (ha i h)⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOfFinOrderOfBounded
section
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GamFree

theorem pow_bounded {n : ℕ} (g x b A : Matrix (Fin n) (Fin n) ℂ) (hx : x.det ≠ 0)
    (hb : b.BlockTriangular id) (hA : A.IsHermitian) (hm : ∀ i, FD.lminor A i ≠ 0)
    (hg : g * x = x * b) (hbA : bᵀ * A * b.map (starRingEnd ℂ) = A) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by
  first
  | exact @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry
  | exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry
  | (apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)
  | (intros; apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry ..)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_unitary (G γ : Matrix (Fin r) (Fin r) E)
    (hγ : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : FD.gram τ G (γ.map τ * Y) = FD.gram τ G Y := by
  have h : FD.gram τ G (γ.map τ) = G.map τ := by
    ext a b
    have := congrArg τ (hγ (Pi.single a 1) (Pi.single b 1))
    have h0 : FD.cc (0 : E) = 0 := by simp [FD.cc]
    have h1 : FD.cc (1 : E) = 1 := by simp [FD.cc]
    have e : FD.herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
      simp [FD.herm, Pi.single_apply, apply_ite FD.cc, h0, h1]
    rw [e] at this
    rw [Matrix.map_apply, ← this]
    simp [FD.gram, FD.hermC, FD.herm, FD.col, FD.emb_cc]
  rw [FD.FrameDegreeData.gram_mul, h, FD.FrameDegreeData.gram_eq]

omit [IsCMField E] in

theorem isOfFinOrder_of_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (γ : GL (Fin r) E)
    (hγ : ∀ v ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ Λ) (R : ℝ)
    (hR : ∀ (τ : Ψ) (k : ℕ) (a b : Fin r), ‖τ.1 (((γ : Matrix (Fin r) (Fin r) E) ^ k) a b)‖ ≤ R) :
    IsOfFinOrder γ := by
  by_contra hfin
  have hinj := injective_pow_iff_not_isOfFinOrder.mpr hfin
  obtain ⟨k, hk, hi⟩ := LatFin.exists_common_den Λ hfg
  choose l hl hm using fun b : Fin r => LatFin.exists_int_smul_mem Λ hsp (Pi.single b 1)
  have hS := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    LatFin.finite_bounded Ψ hΨ (k * l b) (mul_ne_zero hk (hl b)) R
  have hpow : ∀ n : ℕ, ∀ v ∈ Λ, ((γ : Matrix (Fin r) (Fin r) E) ^ n) *ᵥ v ∈ Λ := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (hγ v hv)
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => fun a b => ((γ : Matrix (Fin r) (Fin r) E) ^ n) a b) (fun m n h => ?_)
    (fun n => ?_) hS
  · apply hinj
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    exact h
  · intro a b
    refine ⟨?_, fun τ => hR τ n a b⟩
    have := hi _ (hpow n _ (hm b)) a
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
    rw [Int.cast_mul, mul_assoc, ← zsmul_eq_mul _ (l b)]
    exact this

omit [IsCMField E] in

noncomputable def restrict (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ Λ) : Λ ≃ₗ[ℤ] Λ where
  toFun v := ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ v, (hγ _).1 v.2⟩
  invFun v := ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, (hγ _).2 (by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact v.2)⟩
  map_add' v w := Subtype.ext (Matrix.mulVec_add (γ : Matrix (Fin r) (Fin r) E) (v : Fin r → E) w)
  map_smul' c v := Subtype.ext (Matrix.mulVec_smul (γ : Matrix (Fin r) (Fin r) E) c (v : Fin r → E))
  left_inv v := Subtype.ext (by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
  right_inv v := Subtype.ext (by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])

theorem gam_free : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.IsUStab Gm Λ γ → (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w) → ∀ x ∈ FD.GG Ψ Gm p0, ∀ b ∈ FD.Bor Ψ r, FD.lact γ x = FD.rmul x b → γ = 1 := by
  intro hMink E _ _ _ r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM hγ hcong x hx b hb hxb
  have hbd : ∀ τ : Ψ, ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin r),
      ‖((((γ : Matrix (Fin r) (Fin r) E)).map τ.1) ^ k) i j‖ ≤ R := by
    intro τ
    have hg : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * FD.mat x τ = FD.mat x τ * FD.mat b τ :=
      congrFun hxb τ
    refine pow_bounded _ (FD.mat x τ) (FD.mat b τ) (FD.gram τ.1 Gm (FD.mat x τ)) (hx τ).1
      (fun a c h => (hb τ).2 a c h) (FD.gram_isHermitian τ.1 hG _) (fun i h0 => ?_) hg ?_
    · have h := (hx τ).2 i
      have : FD.dmin Gm x τ i = 0 := h0
      rw [this] at h
      simp at h
    · rw [← FD.FrameDegreeData.gram_mul, ← hg, gram_unitary Gm _ hγ.1]
  choose R hR using hbd
  have hfo : IsOfFinOrder γ := by
    refine isOfFinOrder_of_bounded Ψ hΨ Λ hfg hsp γ (fun v hv => (hγ.2 v).1 hv) (∑ τ, |R τ|)
      fun τ k a c => ?_
    have h1 := hR τ k a c
    rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)))
  obtain ⟨n, hn, hγn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : Module.Free ℤ Λ := inferInstance
  have hpow : ∀ (k : ℕ) (v : Λ), (((restrict Λ γ hγ.2) ^ k) v : Fin r → E) =
      ((γ : Matrix (Fin r) (Fin r) E) ^ k) *ᵥ v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]
      rfl
  have hσ := hMink Λ (restrict Λ γ hγ.2) n M hn (by
    ext v : 1
    apply Subtype.ext
    rw [hpow, ← Units.val_pow_eq_pow_val, hγn]
    simp) hM (fun y => by
      obtain ⟨w, hw, h⟩ := hcong y y.2
      exact ⟨⟨w, hw⟩, Subtype.ext h⟩)
  have hfix : ∀ v ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
    have := hpow 1 ⟨v, hv⟩
    rw [hσ] at this
    simpa using this.symm
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on hsp
  intro v hv
  simpa using hfix v hv

end GlobalTheory.GamFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliPointFromFgSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem point_from_fg_subalgebra {K F : Type} [CommRing K] [CommRing F] (φ : K →+* F) {X : Scheme.{0}}
    (s : X ⟶ Sp K) [LocallyOfFinitePresentation s] (S : Type) [CommRing S] [Algebra F S] (x : Sp S ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap F S).comp φ)) :
    ∃ S₀ : Subalgebra F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ X, x₀ ≫ s = spMap ((algebraMap F S₀).comp φ) ∧
      spMap S₀.val.toRingHom ≫ x₀ = x := by
  classical
  let P : Finset S ⥤ CommRingCat.{0} :=
    { obj t := .of (Algebra.adjoin F (t : Set S))
      map {t t'} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cP : Cocone P :=
    { pt := .of S
      «ι» := { app t := CommRingCat.ofHom (Algebra.adjoin F (t : Set S)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcP : IsColimit cP := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : S := x
        exact ⟨({x'} : Finset S), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin F (({x'} : Finset S) : Set S)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset S)ᵒᵖ ⥤ Scheme.{0} := P.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cP.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcP.op
  let κ (t : (Finset S)ᵒᵖ) : G.obj t ⟶ Sp K :=
    spMap ((algebraMap F (Algebra.adjoin F (t.unop : Set S))).comp φ)
  have hι {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : G.map f ≫ κ t' = κ t := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (t : (Finset S)ᵒᵖ) : cG.π.app t ≫ κ t = spMap ((algebraMap F S).comp φ) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hG (t : (Finset S)ᵒᵖ) : IsAffine (G.obj t) := inferInstanceAs (IsAffine (Spec _))
  have hGa {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : IsAffineHom (G.map f) := inferInstance
  obtain ⟨i, y₀, hy₀, hy₁⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G
    ({ app := κ, naturality := fun t t' f => (hι f).trans (Category.comp_id _).symm } :
      G ⟶ (Functor.const _).obj (Sp K)) s cG hcG x
    (NatTrans.ext (funext fun t => (hι' t).trans hx.symm))
  exact ⟨Algebra.adjoin F (i.unop : Set S), ⟨i.unop, rfl⟩, y₀, hy₁, hy₀⟩

theorem moduli_point_from_fg_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∃ S₀ : Subalgebra c.F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ Xo.X, x₀ ≫ Xo.s = sOf c S₀ ∧ spMap S₀.val.toRingHom ≫ x₀ = x := by
  intro E _ _ _ H Dw l Xo c S _ _ x hx
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  exact point_from_fg_subalgebra (IntermediateField.inclusion c.le).toRingHom Xo.s S x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem reduced_finiteType_iff_testRing :
    ∀ (K : Type) [Field K], (∀ (R : Type) [CommRing R] [Algebra K R], Algebra.FiniteType K R → IsReduced R → ∃ p : TRing K, Nonempty (p.R ≃ₐ[K] R)) ∧ ∀ p : TRing K, Algebra.FiniteType K p.R ∧ IsReduced p.R := by
  intro K _
  refine ⟨fun R _ _ hft hred => ?_, fun p => ⟨inferInstance, ?_⟩⟩
  · obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
    have hrad : (RingHom.ker f).IsRadical := by
      intro x hx
      obtain ⟨m, hm⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hm
      exact (RingHom.mem_ker).2 (IsReduced.eq_zero _ ⟨m, hm⟩)
    exact ⟨⟨n, RingHom.ker f, hrad⟩, ⟨Ideal.quotientKerAlgEquivOfSurjective hf⟩⟩
  · exact (Ideal.isRadical_iff_quotient_reduced p.I).1 p.3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.SecCalc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a * b))) = _
  rw [map_mul, map_mul, map_mul]
  rfl

theorem scal_add' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a + b) i = scal x a i + scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a + b))) = _
  rw [map_add, map_add, map_add]
  rfl

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S 1)) = _
  rw [map_one, map_one, map_one]

theorem ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
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

theorem scal_pull' {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem pm_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Y : Scheme.{0}} (p q : Y ⟶ Gx x)
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

theorem pm_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) : ∃ pm : Gx x' ⟶ Gx x,
      pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ :=
  ⟨pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition), pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem secBC_iff {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) :
    SecBC φ a x x' s s' ↔ ∀ i : Fin 1 → Xo.univ.t.PP.L.ι,
      s'.f i = scal x' (φ a) i * (pm.appLE _ _ (ppx_le pm hs i)).hom (s.f i) := by
  constructor
  · rintro ⟨q, qs, qf, ha⟩ i
    obtain rfl : q = pm := pm_ext _ _ (qs.trans hs.symm) (qf.trans hf.symm)
    rw [← ha i (ppx_le q hs i), map_mul, scal_pull' φ q hf]
  · intro h
    refine ⟨pm, hs, hf, fun i hi => ?_⟩
    rw [h i, map_mul, scal_pull' φ pm hf]

theorem sec_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  intro E _ _ _ H Dw l Xo S T U _ _ _ φ ψ x x' x'' hx hx'
  obtain ⟨p, ps, pf⟩ := pm_exists φ hx
  obtain ⟨q, qs, qf⟩ := pm_exists ψ hx'
  refine ⟨fun a s s' s'' h => ?_, fun a s t => ?_, fun a s s' t' h => ?_,
    fun a b i => ⟨scal_mul' x a b i, scal_add' x a b i, scal_one' x i⟩⟩
  · have rs : (q ≫ p) ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x'') Xo.univ.t.G).left := by
      rw [Category.assoc, ps, qs]
    have rf : (q ≫ p) ≫ (fst (Over.mk x) Xo.univ.t.G).left =
        (fst (Over.mk x'') Xo.univ.t.G).left ≫ spMap (ψ.comp φ) := by
      rw [Category.assoc, pf, ← Category.assoc, qf, Category.assoc, spMap_comp']
    rw [secBC_iff φ a p ps pf] at h
    rw [secBC_iff ψ 1 q qs qf, secBC_iff (ψ.comp φ) a (q ≫ p) rs rf]
    refine forall_congr' fun i => ?_
    have e : (q ≫ p).appLE _ _ (ppx_le (q ≫ p) rs i) = p.appLE _ _ (ppx_le p ps i) ≫ q.appLE _ _ (ppx_le q qs i) :=
      (Scheme.Hom.appLE_comp_appLE q p _ _ _ _ _).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, h i, map_one, scal_one' x'' i, _root_.one_mul, map_mul,
      scal_pull' ψ q qf]
    rfl
  · rw [secBC_iff (RingHom.id S) a (𝟙 (Gx x)) (Category.id_comp _)
      (by rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm)]
    refine forall_congr' fun i => ?_
    have e : ∀ hh : (PPx x).U i ≤ (𝟙 (Gx x) : Gx x ⟶ Gx x) ⁻¹ᵁ (PPx x).U i,
        (𝟙 (Gx x) : Gx x ⟶ Gx x).appLE _ _ hh = 𝟙 _ := by
      intro hh
      exact (Scheme.Hom.appLE_eq_app (𝟙 (Gx x) : Gx x ⟶ Gx x)).trans (Scheme.Hom.id_app _)
    rw [e]
    rfl
  · rw [secBC_iff φ 1 p ps pf] at h
    rw [secBC_iff φ a p ps pf]
    refine forall_congr' fun i => ?_
    rw [h i, map_one, scal_one' x' i, _root_.one_mul]

end GlobalTheory.Frames.SecCalc
end
end

