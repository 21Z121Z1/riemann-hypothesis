import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0182
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0186
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatGenFrameComplexCompat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

section Comb

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem epsMul_zero_eq : GlobalTheory.CompanionTheory.Ar.epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsMul_one_eq : GlobalTheory.CompanionTheory.Ar.epsMul (1 : R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul]

theorem comp_one_over {Y Z M : Over S} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  exact MonObj.comp_one f

theorem prod_ofFn_single {M : Type*} [Monoid M] : ∀ {n : ℕ} (u : Fin n → M) (j : Fin n),
    (∀ i, i ≠ j → u i = 1) → (List.ofFn u).prod = u j := by
  intro n
  induction n with
  | zero => intro u j; exact j.elim0
  | succ n ih =>
    intro u j hu
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1 := List.prod_eq_one fun x hx => by
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hu _ (Fin.succ_ne_zero i)
      rw [h1, _root_.mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      rw [hu 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]
      exact ih (fun i => u i.succ) j' fun i hi => hu _ fun h => hi (Fin.succ_injective _ h)

theorem isComb_single {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (w : Fin n → (epsAt x ⟶ G))
    (hw : ∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (w i)) (j : Fin n) : GlobalTheory.CompanionTheory.Ar.Fl.IsComb (Pi.single j 1) w (w j) := by
  classical
  refine ⟨fun i => if i = j then w i else 1, fun i => ?_, ?_⟩
  · show Over.Hom.left (if i = j then w i else 1) = _
    by_cases hij : i = j
    · subst hij
      simp [epsMul_one_eq, spMap]
    · rw [if_neg hij, Pi.single_eq_of_ne hij, epsMul_zero_eq]
      have h1 := comp_one_over (M := G)
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))) rfl :
          GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ Over.mk x)
      rw [← h1, Over.comp_left, ← hw i]
      simp [spMap]
  · rw [prod_ofFn_single _ j fun i hi => if_neg hi, if_pos rfl]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem eq_mul_of_frames {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p}
    {w w' : Vecs y D.q} (h : IsFramed U τ β y v w) (h' : IsFramed U τ β y v' w') {b : F}
    (hb : φ F y v' w' = b * φ₀ F y v' w') : φ F y v w = b * φ₀ F y v w := by
  have hv := h.2.2.1
  have hw := h.2.2.2
  have hv' := h'.2.2.1
  have hw' := h'.2.2.2
  have hvw' : IsFramed U τ β y v w' := ⟨h.1, h.2.1, hv, hw'⟩
  let A : Matrix (Fin D.p) (Fin D.p) F := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose
  have hA : ∀ a, IsComb (A a) v (v' a) := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose_spec
  let B : Matrix (Fin D.q) (Fin D.q) F := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose
  have hB : ∀ b, IsComb (B b) w (w' b) := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose_spec
  have hIv : ∀ a, IsComb ((1 : Matrix (Fin D.p) (Fin D.p) F) a) v (v a) := fun a => by
    have h1 : (1 : Matrix (Fin D.p) (Fin D.p) F) a = Pi.single a 1 :=
      funext fun b => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single v (fun i => (hv.1 i).1) a
  have hIw : ∀ b, IsComb ((1 : Matrix (Fin D.q) (Fin D.q) F) b) w' (w' b) := fun b => by
    have h1 : (1 : Matrix (Fin D.q) (Fin D.q) F) b = Pi.single b 1 :=
      funext fun b' => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single w' (fun i => (hw'.1 i).1) b
  have e1 := hφ.chg F β y v w v w' 1 B h hvw' hIv hB
  have e1₀ := hφ₀.chg F β y v w v w' 1 B h hvw' hIv hB
  have e2 := hφ.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  have e2₀ := hφ₀.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  rw [Matrix.det_one, _root_.mul_one] at e1 e1₀ e2 e2₀
  have hBne : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact hφ.ne F β y v w' hvw' e1
  apply mul_right_cancel₀ hBne
  calc φ F y v w * B.det = φ F y v w' := e1.symm
    _ = φ F y v' w' * A.det := e2.symm
    _ = b * (φ₀ F y v' w' * A.det) := by rw [hb, _root_.mul_assoc]
    _ = b * φ₀ F y v w * B.det := by rw [e2₀, e1₀, _root_.mul_assoc]

theorem ratio_at {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {a : ℂ}
    (ha : ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w)
    {k : Type} [Field k] {β₀ : c.F →+* k} {y₀ : Sp k ⟶ Xo.XF c} {v₀ : Vecs y₀ D.p} {w₀ : Vecs y₀ D.q}
    (h₀ : IsFramed U τ β₀ y₀ v₀ w₀)
    (hb : ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p)
      (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧
        (∀ a, (v' a).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (v₀ a).left) ∧
        ∀ b, (w' b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (w₀ b).left)
    (j : k →+* ℂ) (hj : j.comp β₀ = algebraMap c.F ℂ) : j (φ k y₀ v₀ w₀) = a * j (φ₀ k y₀ v₀ w₀) := by
  obtain ⟨v', w', hfr, hv', hw'⟩ := hb ℂ j
  have hfr' : IsFramed U τ (algebraMap c.F ℂ) (spMap j ≫ y₀) v' w' := by
    rw [← hj]
    exact hfr
  have e := ha _ v' w' hfr'
  rw [hφ.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw',
    hφ₀.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw'] at e
  exact e

theorem flatGen_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : c.F, a ≠ 0 ∧ ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w = β a * φ₀ F y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  obtain ⟨a, ha⟩ := GlobalTheory.T.flat_gen_frame_independent E H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  have hL := hφ.line
  have hL₀ := hφ₀.line
  by_cases hex : ∃ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q),
      IsFramed U τ (algebraMap c.F ℂ) y v w
  · obtain ⟨y1, v1, w1, h1⟩ := hex
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ ℂ (algebraMap c.F ℂ) y1 v1 w1 h1
    have hr := ratio_at hL hL₀ ha h₀ hb j hj
    have hne₀ : j (φ₀ k y₀ v₀ w₀) ≠ 0 := (map_ne_zero j).2 (hL₀.ne k β₀ y₀ v₀ w₀ h₀)
    have hfix : ∀ σ' : ℂ ≃+* ℂ, (∀ x ∈ c.F, σ' x = x) → σ' a = a := by
      intro σ' hσ'
      have hj' : (σ'.toRingHom.comp j).comp β₀ = algebraMap c.F ℂ := by
        refine RingHom.ext fun x => ?_
        have hx := RingHom.congr_fun hj x
        simp only [RingHom.comp_apply] at hx ⊢
        rw [hx]
        exact hσ' _ x.2
      have hr' := ratio_at hL hL₀ ha h₀ hb _ hj'
      simp only [RingHom.comp_apply] at hr'
      rw [hr, map_mul] at hr'
      exact mul_right_cancel₀ ((map_ne_zero _).2 hne₀) hr'
    have haF : a ∈ c.F := GlobalTheory.T.fixed_by_automorphisms_mem_field c.F a c.fin hfix
    refine ⟨⟨a, haF⟩, ?_, ?_⟩
    · intro h0
      have ha0 : a = 0 := congrArg Subtype.val h0
      apply hL.ne k β₀ y₀ v₀ w₀ h₀
      apply j.injective
      rw [hr, map_zero, ha0, zero_mul]
    · intro F _ β y v w hfr
      obtain ⟨k', _, β₀', y₀', v₀', w₀', f', j', h₀', hfβ', hj'', hy', hb'⟩ :=
        GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
      subst hy'
      subst hfβ'
      have hr2 := ratio_at hL hL₀ ha h₀' hb' j' hj''
      have hk : φ k' y₀' v₀' w₀' = β₀' ⟨a, haF⟩ * φ₀ k' y₀' v₀' w₀' := by
        apply j'.injective
        rw [map_mul, hr2]
        congr 1
        have hx := RingHom.congr_fun hj'' ⟨a, haF⟩
        simp only [RingHom.comp_apply] at hx
        rw [hx]
        rfl
      obtain ⟨v', w', hfr', hv', hw'⟩ := hb' F f'
      have n1 := hL.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      have n2 := hL₀.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      refine eq_mul_of_frames hL hL₀ hfr hfr' (b := f' (β₀' ⟨a, haF⟩)) ?_
      rw [n1, n2, hk, map_mul]
  · refine ⟨1, one_ne_zero, fun F _ β y v w hfr => ?_⟩
    exfalso
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
    obtain ⟨v', w', hfr', -, -⟩ := hb ℂ j
    rw [hj] at hfr'
    exact hex ⟨_, v', w', hfr'⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFirst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgLie

section Modules

theorem mem_of_mem_iSup {Ω E I : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (A : Subring Ω)
    (W : I → Submodule Ω E) (hW : iSupIndep W) (N : I → Submodule A E) (hN : ∀ s, ∀ x ∈ N s, x ∈ W s)
    {e : E} (s₀ : I) (he : e ∈ ⨆ s, N s) (hs : e ∈ W s₀) : e ∈ N s₀ := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp N e).1 he
  have hsum : (f.sum fun _ x => x) - f s₀ = ∑ i ∈ f.support.erase s₀, f i := by
    by_cases h0 : s₀ ∈ f.support
    · rw [Finsupp.sum, ← Finset.add_sum_erase _ _ h0]
      abel
    · rw [Finsupp.sum, Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0, sub_zero]
  have h1 : (f.sum fun _ x => x) - f s₀ ∈ W s₀ := sub_mem hs (hN _ _ (hf s₀))
  have h2 : (f.sum fun _ x => x) - f s₀ ∈ ⨆ (k) (_ : k ≠ s₀), W k := by
    rw [hsum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hk) (hN _ _ (hf k)))
  have h3 := (Submodule.disjoint_def.1 (hW s₀)) _ h1 h2
  rw [sub_eq_zero.1 h3]
  exact hf s₀

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (e : E) : e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

end Modules

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

theorem not_inFibre_push {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀}
    {i : Ω₀ →+* Ω} (hξ : IsCptGen ξ) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i) (q : Cpt ξ) {r : ℕ}
    (hq : ¬ InFibre ξ r q) : ¬ InFibre ξ₀ r (pushCpt hd q) := by
  intro hf
  apply hf
  obtain ⟨h0, -, s, hs⟩ : unitAt ξ q (r : Ω) := not_not.1 hq
  have hmul : (r : X.presheaf.stalk q.1) * s = 1 := hξ.inj q (by
    rw [map_mul, map_one, map_natCast, hs]
    exact mul_inv_cancel₀ h0)
  have hu : IsUnit (r : X.presheaf.stalk q.1) := IsUnit.of_mul_eq_one _ hmul
  have hu₀ : IsUnit (r : X₀.presheaf.stalk (h q.1)) :=
    isUnit_of_map_unit (h.stalkMap q.1).hom _ (by rwa [map_natCast])
  have h0' : (r : Ω₀) ≠ 0 := fun e => h0 (by rw [← map_natCast i, e, map_zero])
  refine ⟨h0', ⟨_, map_natCast (genMap ξ₀ (pushCpt hd q)) r⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu₀
  refine ⟨(u⁻¹ : (X₀.presheaf.stalk (h q.1))ˣ).val, ?_⟩
  have e1 : genMap ξ₀ (pushCpt hd q) u.val = (r : Ω₀) := (congrArg _ hu').trans (map_natCast _ r)
  exact (map_units_inv (genMap ξ₀ (pushCpt hd q)) u).trans (congrArg Inv.inv e1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_inj_of_pull {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) {ξ : Spec (CommRingCat.of Ω) ⟶ S'} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G' ξ V) {e e' : V}
    (h : (M.pt e).left ≫ φ = (M.pt e').left ≫ φ) : e = e' :=
  M.inj (Over.OverMorphism.ext (hG.1.hom_ext h ((Over.w _).trans (Over.w _).symm)))

theorem exists_value_up {t : SAB H X₀} {t' : SAB H X} {f : X ⟶ X₀} (m : SABMap t' t f)
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {i : Ω₀ →+* Ω}
    (hall : ∀ q : X, genPt ξ ⤳ q) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) {V V' : Type} [AddCommGroup V] [Module Ω₀ V]
    [AddCommGroup V'] [Module Ω V'] {M : LieModel t.G ξ₀ V} {M' : LieModel t'.G ξ V'} {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) {e : V} {v₀ : epsAt (z ≫ f) ⟶ t.G} (hv : M.ValAt (z ≫ f) e v₀) :
    ∃ v : epsAt z ⟶ t'.G, M'.ValAt z (j e) v ∧ v₀.left = v.left ≫ m.φ := by
  obtain ⟨h₀, w, hw, hwz⟩ := hv
  have hp : genPt ξ₀ ⤳ f (centre z) := h₀
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap (centre z)).hom) ≫ X₀.fromSpecStalk (f (centre z)) =
      X.fromSpecStalk (centre z) ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ ⟨centre z, hall _⟩).comp (f.stalkMap (centre z)).hom = i.comp (genMap ξ₀ ⟨f (centre z), hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd _ (hall _) hp)
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨centre z, hall _⟩
  obtain ⟨u, hu, huφ⟩ := LiePull.ext_up (A := X₀.presheaf.stalk (f (centre z))) (A' := X.presheaf.stalk (centre z))
    (g := genMap ξ₀ ⟨f (centre z), hp⟩) (g' := genMap ξ ⟨centre z, hall _⟩) (ρ := (f.stalkMap (centre z)).hom)
    (x := X₀.fromSpecStalk (f (centre z))) (x' := X.fromSpecStalk (centre z)) (M := M) (M' := M') (j := j) m.cart hj hρ
    hρ' hx' hw
  have hc : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  refine ⟨LieCarrier.epsHom _ _ z hc ≫ u, ⟨hall _, u, hu, rfl⟩, ?_⟩
  have e1 : (LieCarrier.epsHom _ _ z hc ≫ u).left =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ u.left := rfl
  have e2 : (Scheme.stalkClosedPointTo (z ≫ f)).hom =
      (Scheme.stalkClosedPointTo z).hom.comp (f.stalkMap (centre z)).hom := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have e4 : spMap (dualMap (Scheme.stalkClosedPointTo (z ≫ f)).hom) =
      spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ spMap (dualMap (f.stalkMap (centre z)).hom) := by
    rw [e2]
    exact (congrArg spMap (LiePull.dualMap_comp (f.stalkMap (centre z)).hom (Scheme.stalkClosedPointTo z).hom).symm).trans
      (spMap_comp' _ _)
  have e3 : (LieCarrier.epsHom _ _ z hc ≫ u).left ≫ m.φ = spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫
      spMap (dualMap (f.stalkMap (centre z)).hom) ≫ w.left :=
    (congrArg (· ≫ m.φ) e1).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ ·) huφ))
  exact hwz.trans (((congrArg (· ≫ w.left) e4).trans (Category.assoc _ _ _)).trans e3.symm)

end Points

section Main

theorem lie_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl hβ hcov hfl
  obtain ⟨-, hf, hcst⟩ := hcov
  obtain ⟨m₀, hφ⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  obtain ⟨j, hpt, hsemi, hind, -, hpull⟩ := GlobalTheory.T.lie_model_dominant_hodge E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ Ω₀ Ω 𝔐₀.ξ 𝔐.ξ i 𝔐₀.Li 𝔐.Li 𝔐₀.M 𝔐.M
    𝔐₀.tie.gen 𝔐.tie.gen hd
  have hact : ∀ a e, 𝔐.ρ a (j e) = j (𝔐₀.ρ a e) := fun a e => pt_inj_of_pull m₀.cart 𝔐.M (by
    have e1 := congrArg CommaMorphism.left (𝔐.act a (j e))
    have e2 := congrArg CommaMorphism.left (𝔐₀.act a e)
    have e3 := m₀.act a
    rw [hpt]
    refine (congrArg (· ≫ m₀.φ) e1).trans ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine (congrArg (_ ≫ ·) e3).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (𝔐₀.t.act.act a).left) (hpt e)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (spMap (dualMap i) ≫ ·) e2.symm)
  have hemb : ∀ s, 𝔐.emb s = i.comp (𝔐₀.emb s) := fun s => by
    simp only [HodgeCpt.emb, hcst, RingHom.comp_assoc]
  have heig : ∀ s e, e ∈ 𝔐₀.Vgen s → j e ∈ 𝔐.Vgen s := fun s e he => by
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [hact, (mem_eigSp_iff _ _ _).1 he a, hsemi, hemb]
    rfl
  refine ⟨j, hsemi, hind, fun s a => ?_, fun q hq s => ?_, fun z r b Γ hΓ => ?_⟩
  · refine pt_inj_of_pull 𝔐.m.cart 𝔐.M ?_
    have e1 : (𝔐.M.pt (j (Fl₀.b s a))).left ≫ 𝔐.m.φ =
        spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ := by
      rw [hφ, ← Category.assoc, hpt, Category.assoc]
    exact e1.trans (hfl s a).symm
  · have hq₀ : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐₀.ξ r (pushCpt hd q) :=
      fun r hr => not_inFibre_push 𝔐.tie.gen hd q (hq r hr)
    obtain ⟨hV, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y 𝔐 hβ q hq
    obtain ⟨hV₀, -, hlat₀⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ hβ (pushCpt hd q) hq₀
    obtain ⟨-, -, -, -, -, -, hindep, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
    rw [hV s, hV₀ s]
    let N : (CMType H ⊕ CMType H) → Submodule (regAt 𝔐.ξ q) 𝔐.Li := fun s' =>
      Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.dR s' (pushCpt hd q) : Set 𝔐₀.Li))
    have hle : ∀ s', N s' ≤ 𝔐.dR s' q := fun s' => by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, he, rfl⟩
      refine ⟨?_, heig s' e he.2⟩
      rw [hpull]
      exact Submodule.subset_span ⟨hd.specializes q, e, he.1, rfl⟩
    have htop : 𝔐.M.lat q ≤ ⨆ s', N s' := by
      rw [hpull]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ ⨆ s', 𝔐₀.dR s' (pushCpt hd q) := hlat₀ ▸ he
      refine Submodule.iSup_induction _ (motive := fun x => j x ∈ ⨆ s', N s') he' (fun s' x hx => ?_) ?_ ?_
      · exact Submodule.mem_iSup_of_mem s' (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro x x' hx hx'
        rw [map_add]
        exact Submodule.add_mem _ hx hx'
    refine le_antisymm (fun e he => ?_) (hle s)
    exact mem_of_mem_iSup _ 𝔐.Vgen hindep N (fun s' x hx => (hle s' hx).2) s (htop he.1) he.2
  · obtain ⟨v₀, hv₀, hIP⟩ := hΓ
    choose v hv hvφ using fun k => exists_value_up m₀ 𝔐.all hd hpt z (hv₀ k)
    exact ⟨v, hv, fun p q => (GlobalTheory.T.hodge_inner_product_map_iff E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ z (v p) (v q) (v₀ p) (v₀ q) (Γ p q) (hvφ p) (hvφ q)).2 (hIP p q)⟩

end Main

end GlobalTheory.CompanionTheory.Ar.ChgLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (n : ℕ) (ix : Fin n → Fin r), Function.Injective ix → (gramAt h z fun l => B (ix l)).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelLocalizationAtPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_localization_at_prime : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A]
    [IsLocalization.AtPrime A 𝔭] [Algebra A L] [IsScalarTower (𝓞 L) A L] (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) (f : Module.Dual Ω Li)
    (h : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) A) ≫ z)), IsCptGen ξ →
    (∀ e ∈ M.lat ⟨_, h⟩, f e ∈ regAt ξ ⟨_, h⟩) →
    (∀ h' : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z), ∀ e ∈ M.lat ⟨_, h'⟩, f e ∈ regAt ξ ⟨_, h'⟩) →
    ∃ g : B.carrier →ₗ[𝓞 L] A,
      (∀ (x : B.carrier) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (u : L),
        M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x v →
        ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (f e) u → algebraMap A L (g x) = u) ∧
      ∀ (e : Li) (u : A), e ∈ M.lat ⟨_, h⟩ → ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) u →
        ∃ (d : 𝓞 L) (n : ℕ) (x x' : B.carrier) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
          d ∉ 𝔭 ∧ n ≠ 0 ∧ g x = algebraMap (𝓞 L) A d * u ∧ M.ValAt _ ((n : Ω) • e) v ∧
          MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v ∧ (n : 𝓞 L) • x = d • x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinLie.exists_integral_form | exact GlobalTheory.CompanionTheory.Ar.RootHt.FinLie.exists_integral_form | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.FinLie.exists_integral_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointFrameSpecialization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameVal

theorem exists_framed_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ y h hO hτ _ hy hf₁ hf₂
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  have hfib : (⟨centre (y ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib :=
    ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), by simp only [Model.j, centre, Scheme.Hom.comp_apply]⟩
  obtain ⟨g, b, hb, hS⟩ := h3 _ hfib
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists Y.X Y.t.G ℂ (y ≫ Y.j)
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M ℂ (y ≫ Y.j) h ER MR Z.gen inferInstance
  have hval : ∀ {n : ℕ} (τ' : E →+* ℂ) (e : Fin n → Z.V), (Z.eig τ').IsFrameAt e ⟨centre (y ≫ Y.j), h⟩ →
      ∀ i, ∃ w, Z.M.ValAt (y ≫ Y.j) (e i) (MR.pt w) := fun τ' e hf i => by
    have hmem : e i ∈ Z.eig τ' ⟨centre (y ≫ Y.j), h⟩ := by
      rw [hf.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨ev ⟨e i, hmem.1⟩, (hev _ _).2 ⟨hmem.1, rfl⟩⟩
  choose w₁ hw₁ using hval τ b₁ hf₁
  choose w₂ hw₂ using hval _ b₂ hf₂
  choose v hv using fun i => exists_sameVec_left Y y (MR.pt (w₁ i))
  choose w hw using fun j => exists_sameVec_left Y y (MR.pt (w₂ j))
  obtain ⟨hL₁, hL₂⟩ := GlobalTheory.CompanionTheory.Ar.LocFrames.lieMult_at y σ τ hy hτ
  refine ⟨v, w, ⟨hy, Set.subset_univ _, ?_, ?_⟩, fun i => ⟨_, hw₁ i, hv i⟩, fun j => ⟨_, hw₂ j, hw j⟩⟩
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y τ D.p b₁ v (fun i => MR.pt (w₁ i)) h hO.2.2 hy hL₁
      ⟨g, b, hb, hS τ⟩ hf₁ hw₁ hv
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y _ D.q b₂ w (fun j => MR.pt (w₂ j)) h hO.2.2 hy hL₂
      ⟨g, b, hb, hS _⟩ hf₂ hw₂ hw

end GlobalTheory.CompanionTheory.Ar.FrameVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannLatticeOverPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_lattice_over_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ), IsOver 𝔐 z κ p → FibreLat Xo.univ.t p R → FibreLat 𝔐.t z R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver <;> assumption)
end

