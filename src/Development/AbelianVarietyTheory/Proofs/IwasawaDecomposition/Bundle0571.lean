import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Flags

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  {ty ty' : (E →+* ℂ) → Finset ℕ}

attribute [local instance] Over.cartesianMonoidalCategory

theorem comb_bc (φ : R →+* S) {x : Sp R ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem comb_push_iff {f : X' ⟶ X} (mu : SABMap t' t f) {x : Sp R ⟶ X'} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t'.G.left)} (hv : ∀ i, IsTanAtG t' x (v i)) (cf : Fin m → R)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : IsTanAtG t' x w) :
    IsCombAtG t (x ≫ f) (fun i => v i ≫ mu.φ) cf (w ≫ mu.φ) ↔ IsCombAtG t' x v cf w := by
  refine (isComb_iff (fun i => pushE mu x rfl (tanOf (hv i))) cf (pushE mu x rfl (tanOf hw))).trans
    (Iff.trans ?_ (isComb_iff (fun i => tanOf (hv i)) cf (tanOf hw)).symm)
  rw [← (pushE mu x rfl).injective.eq_iff, map_sum]
  simp only [map_smul]

theorem Vecs.bc_bc (φ : R →+* S) (ψ : S →+* T) (u : Vecs Dw t R) : (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  have e : (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := RingHom.ext fun z => by ext <;> simp [dualMap]
  simp only [Vecs.bc]
  rw [← Category.assoc, spMap_comp', e]

theorem SameFlag.refl {x : Sp R ⟶ X} {u : Vecs Dw t R} (hu : ∀ τ i, IsTanAtG t x (u τ i)) : SameFlag ty t x u u :=
  fun τ _ _ i hi => ⟨Pi.single i 1, fun _ hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _,
    GlobalTheory.ShFam.isCombAtG_single t x (hu τ) i⟩

theorem SameFlag.mono {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (h : SameFlag ty t x u u') (hle : ∀ σ, ty' σ ⊆ ty σ) :
    SameFlag ty' t x u u' := fun τ k hk => h τ k (hle τ hk)

theorem SameFlag.trans {x : Sp R ⟶ X} {u u' u'' : Vecs Dw t R} (hu : ∀ τ i, IsTanAtG t x (u τ i))
    (hall : ∀ τ i, ∃ cf, IsCombAtG t x (u τ) cf (u' τ i))
    (h : SameFlag ty t x u u') (h' : SameFlag ty t x u' u'') : SameFlag ty t x u u'' := by
  intro τ k hk i hi
  obtain ⟨c, hc, hc'⟩ := h' τ k hk i hi
  have : ∀ j : Fin (Dw.mult τ), ∃ cf : Fin (Dw.mult τ) → R, ((j : ℕ) < k → ∀ j' : Fin (Dw.mult τ), k ≤ (j' : ℕ) → cf j' = 0) ∧
      IsCombAtG t x (u τ) cf (u' τ j) := fun j => by
    by_cases hj : (j : ℕ) < k
    · obtain ⟨a, ha, ha'⟩ := h τ k hk j hj
      exact ⟨a, fun _ => ha, ha'⟩
    · obtain ⟨a, ha⟩ := hall τ j
      exact ⟨a, fun h => absurd h hj, ha⟩
  choose A hA hA' using this
  refine ⟨(Matrix.of fun j' j => A j j').mulVec c, fun j' hj' => ?_, tanLinG _ (hu τ) _ _ _ _ hA' hc'⟩
  show ∑ j, A j j' * c j = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : (j : ℕ) < k
  · simp [hA j hj j' hj']
  · simp [hc j (not_lt.1 hj)]

theorem SameFlag.push {f : X' ⟶ X} (mu : SABMap t' t f) {x : Sp R ⟶ X'} {u u' : Vecs Dw t' R}
    (hu : ∀ τ i, IsTanAtG t' x (u τ i)) (hu' : ∀ τ i, IsTanAtG t' x (u' τ i)) (h : SameFlag ty t' x u u') :
    SameFlag (Dw := Dw) ty t (x ≫ f) (fun σ i => u σ i ≫ mu.φ) (fun σ i => u' σ i ≫ mu.φ) := fun τ k hk i hi =>
  (h τ k hk i hi).imp fun cf hcf => ⟨hcf.1, (comb_push_iff mu (hu τ) cf (hu' τ i)).2 hcf.2⟩

theorem IsFrame.push {l l' : Level H} {c : Coeff l} {c' : Coeff l'} (hc : c.F ≤ c'.F) {f : X' ⟶ X} (mu : SABMap t' t f)
    {g : c'.F →+* R} {x : Sp R ⟶ X'} {u : Vecs Dw t' R} (h : IsFrame t' g x u) :
    IsFrame (Dw := Dw) t (g.comp (IntermediateField.inclusion hc).toRingHom) (x ≫ f) (fun σ i => u σ i ≫ mu.φ) := by
  have e : ∀ τ a, g.comp (IntermediateField.inclusion hc).toRingHom (embK c τ a) = g (embK c' τ a) := fun _ _ => rfl
  refine ⟨fun τ i => ⟨isTan_push mu x rfl (h.1 τ i).1, fun a => ?_⟩, fun τ w hw he => ?_⟩
  · rw [e, Category.assoc, ← mu.act, ← Category.assoc, (h.1 τ i).2 a, Category.assoc]
  · obtain ⟨v, hv⟩ := (pushE mu x rfl).surjective (tanOf hw)
    obtain rfl : (tv v).left ≫ mu.φ = w := congrArg (fun z => (tv z).left) hv
    simp only [comb_push_iff mu (fun i => (h.1 τ i).1) _ (isTan_tv v)]
    refine h.2 τ _ (isTan_tv v) fun a => mu.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, mu.act, ← Category.assoc, he a, e, Category.assoc]
    · rw [Category.assoc, Over.w, Category.assoc, (isTan_tv v).1, ← Category.assoc, spMap_comp']
      congr 2
      ext r <;> simp [epsMul]

theorem IsFrame.exists_comb {l : Level H} {c : Coeff l} {g : c.F →+* R} {x : Sp R ⟶ X} {u u' : Vecs Dw t R}
    (h : IsFrame t g x u) (h' : IsFrame t g x u') (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    ∃! cf, IsCombAtG t x (u τ) cf (u' τ i) := h.2 τ _ (h'.1 τ i).1 (h'.1 τ i).2

end Flags

theorem isDiscreteValuationRing_V {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : IsDiscreteValuationRing (c.V W) := by
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp.ne_zero
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem coeff_ext {l : Level H} {c : Coeff l} {W : ValuationSubring ℂ} {R : Type} [CommRing R] {f g : c.F →+* R}
    (h : spMap (f.comp (c.V W).subtype) = spMap (g.comp (c.V W).subtype)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (c.V W)) (congrArg CommRingCat.Hom.hom (Spec.map_injective h))

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem Mdl.affineOpenChart_comp_structure_eq_spMap (Z : Mdl Y i₀) {R : Type} [CommRing R] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* R) :
    spMap φ ≫ Z.chart a ≫ Z.s = spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) := by
  rw [Z.alg_s, spMap_comp', RingHom.comp_assoc]

theorem Mdl.alg_eq (Z : Mdl Y i₀) {R : Type} [CommRing R] {a a' : Fin Z.m} {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {φ' : Γ(Z.X, (Z.U a').1) →+* R} (h : spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a') :
    φ.comp (Z.alg a) = φ'.comp (Z.alg a') :=
  coeff_ext (W := W) (by rw [← Z.affineOpenChart_comp_structure_eq_spMap, ← Z.affineOpenChart_comp_structure_eq_spMap, reassoc_of% h])

theorem Mdl.exists_chart_fac (Z : Mdl Y i₀) {R : Type} [CommRing R] (w : Sp R ⟶ Z.X) (a : Fin Z.m)
    (h : Set.range w ⊆ (Z.U a).1) : ∃ φ : Γ(Z.X, (Z.U a).1) →+* R, spMap φ ≫ Z.chart a = w := by
  have := (Z.U a).2.isOpenImmersion_fromSpec
  have h' : Set.range w ⊆ Set.range (Z.U a).2.fromSpec := by rwa [(Z.U a).2.range_fromSpec]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (Z.U a).2.fromSpec w h')).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem Mdl.exists_chart (Z : Mdl Y i₀) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (h : Set.range w ⊆ Z.opn) :
    ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k), spMap φ ≫ Z.chart a = w := by
  have h0 := h ⟨IsLocalRing.closedPoint k, rfl⟩
  rw [← Z.cover] at h0
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 h0
  refine ⟨a, Z.exists_chart_fac w a ?_⟩
  rintro _ ⟨x, rfl⟩
  rwa [Subsingleton.elim x (IsLocalRing.closedPoint k)]

theorem exists_isTrans_id (i : Idx H p) :
    ∃ mu : SABMap (Y i).t (Y i).t (𝟙 _), mu.φ = 𝟙 _ ∧ IsTrans (Y := Y) i i (𝟙 _) mu := by
  obtain ⟨mu, hmu⟩ := GlobalTheory.ObjMaps.exists_sab_id (Y i).t
  have e : spMap (RingHom.id (i.c.V W)) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id (i.c.V W))) := by rw [e]; infer_instance
  have hM : i.l.M / i.l.M = 1 := Nat.div_self (by have := i.l.three_le; omega)
  refine ⟨mu, hmu, RingHom.id _, inv (pullback.fst _ _), 𝟙 _, fun _ => rfl, IsIso.inv_hom_id _, ?_, inferInstance,
    by simp, fun a => ?_, fun a => ?_⟩
  · rw [IsIso.inv_comp_eq, pullback.condition]
    exact ((congrArg (_ ≫ ·) e).trans (Category.comp_id _)).symm
  · rw [hM, pow_one, hmu, Category.comp_id, Category.id_comp]
  · rw [Nat.div_self i.l.A_pos, pow_one, hmu, Category.comp_id, Category.id_comp]

theorem exists_isTrans (h : N2 Y) {i i₂ : Idx H p} (hl : i.l.Dvd i₂.l) (hc : i.c.F ≤ i₂.c.F) :
    ∃ (τ : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ), IsTrans i i₂ τ mu := by
  obtain ⟨-, π, hπ, -⟩ := h
  let b : i.c.V W →+* i₂.c.V W :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i₂.c.V W) fun x => x.2
  obtain ⟨π', mu, r, h⟩ := hπ i i₂ hl hc b fun _ => rfl
  exact ⟨_, mu, b, π', r, fun _ => rfl, h⟩

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExists
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.BlockTransporter

theorem exists_unitary_mul_upper {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ t : Matrix (Fin n) (Fin n) ℂ, t.BlockTriangular id ∧ y = u * t := by
  first
  | exact @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | (apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular ..)

theorem exists_unitary_block {r p : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h0 : ∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → B a c = 0) :
    ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ B = u * t := by
  obtain ⟨u, hu, t, ht, e⟩ := exists_unitary_mul_upper B
  have hud : u.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have htd : t.det ≠ 0 := by
    intro h; rw [e, det_mul, h, mul_zero] at hB; exact hB rfl
  letI := invertibleOfIsUnitDet t htd.isUnit
  have hti : (t⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  have hu' : u = B * t⁻¹ := by rw [e, Matrix.mul_nonsing_inv_cancel_right _ _ htd.isUnit]
  refine ⟨u, t, hu, fun a c hc ha => ?_, htd, fun a c h => ht h, e⟩
  rw [hu', mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ c
  · rw [h0 a k (lt_of_le_of_lt (Fin.le_def.1 hk) hc) ha, zero_mul]
  · rw [hti (not_le.1 hk), mul_zero]

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def unitBlock (X : Data E r) : Set (Frame X.Ψ r) :=
  {u | ∀ τ, mat u τ ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
    ∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}

theorem isCompact_unitBlock (X : Data E r) : IsCompact (unitBlock X) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : unitBlock X = ⋂ τ, ({u : Frame X.Ψ r | star (mat u τ) * mat u τ = 1} ∩
        ⋂ a : Fin r, ⋂ c : Fin r, {u | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}) := by
      ext u
      simp only [unitBlock, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      simp only [Matrix.mem_unitaryGroup_iff']
    rw [this]
    refine isClosed_iInter fun τ => IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun c => ?_)
    · have hc : Continuous fun u : Frame X.Ψ r => mat u τ := continuous_apply τ
      exact isClosed_eq (hc.star.matrix_mul hc) continuous_const
    · by_cases h : (c : ℕ) < X.p0 ∧ ¬ (a : ℕ) < X.p0
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = {u | u τ a c = 0} := by
          ext u; simp only [Set.mem_setOf_eq]; exact ⟨fun hu => hu h.1 h.2, fun hu _ _ => hu⟩
        rw [this]
        exact isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ)))
          continuous_const
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = Set.univ := by
          ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro h1 h2; exact absurd ⟨h1, h2⟩ h
        rw [this]; exact isClosed_univ
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun τ => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun a => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun c => ?_
    exact entry_norm_bound_of_unitary (hu τ).1 a c

theorem continuous_rmul (X : Data E r) : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have h1 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.1 τ := (continuous_apply τ).comp continuous_fst
  have h2 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.2 τ := (continuous_apply τ).comp continuous_snd
  exact h1.matrix_mul h2

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

theorem finite_blockTransporter : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom →
    {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
      (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
      ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  intro E _ _ _ r X K hK hKd
  set K' := (fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2) '' (K ×ˢ unitBlock X) with hK'
  have hK'c : IsCompact K' := (hK.prod (isCompact_unitBlock X)).image (continuous_rmul X)
  have hK'd : K' ⊆ X.dom := by
    rintro _ ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
    refine GlobalTheory.PointOfFrames.rmul_mem_dom X (hKd hy) u (fun τ h => ?_) (fun τ => (hu τ).2)
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 (hu τ).1)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hfin := GlobalTheory.PropDiscCompare.compact_of_local X (GlobalTheory.propDisc_of_flagDomainData E r X) (K ∪ K')
    (hK.union hK'c) (Set.union_subset hKd hK'd)
  refine hfin.subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, h0, e⟩
  have key : ∀ τ : X.Ψ, ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ mat b τ = u * t :=
    fun τ => exists_unitary_block (mat b τ) (hb τ) (h0 τ)
  choose u t hu hu0 htd ht hbut using key
  refine ⟨hγ, x, Or.inl hx, rmul y (fun τ => u τ), Or.inr ⟨(y, fun τ => u τ), ⟨hy, fun τ => ⟨hu τ, hu0 τ⟩⟩, rfl⟩,
    fun τ => t τ, fun τ => ⟨htd τ, ht τ⟩, ?_⟩
  rw [e]
  funext τ
  show mat y τ * mat b τ = (mat y τ * u τ) * t τ
  rw [Matrix.mul_assoc, ← hbut τ]

end GlobalTheory.BlockTransporter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRFree

attribute [local instance] Over.cartesianMonoidalCategory

theorem intO_isLocalRing (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : IsLocalRing ↥(intO C) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have hu : ∀ b : ↥(intO C), ‖(b : C)‖ = 1 → IsUnit b := fun b hb => by
    have h0 : (b : C) ≠ 0 := fun h => by simp [h] at hb
    have hi : (b : C)⁻¹ ∈ intO C := by
      show ‖(b : C)⁻¹‖ ≤ 1
      rw [norm_inv, hb, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  have ha : ‖(a : C)‖ ≤ 1 := a.2
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (hu a h)
  · refine Or.inr (hu _ ?_)
    have : ‖(1 : C) + (-(a : C))‖ = max ‖(1 : C)‖ ‖-(a : C)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact h.ne')
    rw [norm_neg, norm_one, max_eq_left h.le, ← sub_eq_add_neg] at this
    exact this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem latDR_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (xO : Sp ↥(intO C) ⟶ X), (∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ xO → xO' = xO) → ∃ (g : ℕ) (v : Fin g → (Sp (DualNumber C) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO C).subtype ≫ xO) (v i)) ∧ (∀ w, IsTanAtG t (spMap (intO C).subtype ≫ xO) w → ∃! cf : Fin g → C, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w) ∧ ∀ (cf : Fin g → C) w, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w → (w ∈ latDR t (spMap (intO C).subtype ≫ xO) ↔ ∀ i, ‖cf i‖ ≤ 1) := by
  intro E _ _ _ H X t C _ _ xO huniq
  have := intO_isLocalRing C
  obtain ⟨n, D, hD, hDb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t (↥(intO C)) xO
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 : ∀ w, IsTanAtG t xO w → ∃! a : Fin n → ↥(intO C), IsCombAtG t xO D a w := by
    have h := hDb _ (RingHom.id ↥(intO C))
    simp only [h1, h3, Category.id_comp] at h
    exact h
  have hDk := fun j => isTanAtG_map t (intO C).subtype (hD j)
  refine ⟨n, fun e => spMap (dualMap (intO C).subtype) ≫ D e, hDk, hDb C _, fun cf w hw => ⟨?_, fun hc => ?_⟩⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := huniq xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (hDb C _ _ (isTanAtG_map t (intO C).subtype hv)).unique hw (comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · let a : Fin n → ↥(intO C) := fun i => ⟨cf i, hc i⟩
    have ha : IsCombAtG t xO D a (combT xO (fun j => ovT (hD j)) a).left :=
      (isCombAtG_iff t xO (fun j => ovT (hD j)) a _).2 rfl
    refine ⟨xO, rfl, _, isTanAtG_of _ (combT_tan _ (fun j => ovT (hD j)) (fun j => smT_zero_ovT _) a), ?_⟩
    have hb := comb_map t (intO C).subtype ha
    exact ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hb).symm.trans
      ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hw)

end GlobalTheory.LatDRFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomain
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FundPre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ae_lact_notMem (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {Bad : Set (Frame X.Ψ r)} (hB : MeasurableSet Bad)
    (hinv : ∀ x, ∀ b ∈ Bor X.Ψ r, (rmul x b ∈ Bad ↔ x ∈ Bad))
    (h0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∀ᵐ z ∂muF X x0, lact γ (cpt X x0 z) ∉ Bad := by
  have hφ : Measurable (Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) :=
    measurable_one.indicator hB
  have hM := measInv_holds (E := E) r X x0 (lact γ x0) ho (KU.isOrth_lact X hγ ho)
    (Bad.indicator 1) hφ (fun x _ b hb => by
      classical
      simp only [Set.indicator_apply, hinv x b hb, Pi.one_apply])
  have h1 : ∫⁻ z, Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
    filter_upwards [h0] with z hz
    exact Set.indicator_of_notMem hz _
  rw [h1, KU.muF_lact X hγ] at hM
  have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X (lact γ x0) z) :=
    hφ.comp (KU.cont_cpt X _).measurable
  have h2 := (lintegral_eq_zero_iff hm).1 hM.symm
  filter_upwards [h2] with z hz hbad
  rw [← KU.cpt_lact] at hbad
  simp only [Set.indicator_of_mem hbad, Pi.one_apply, Pi.zero_apply] at hz
  exact one_ne_zero hz

theorem isFundSet_preimage (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ)
    (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ)
    (hp : X.p0 = r - j)
    (hfree : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1)
    (hnull : ∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 →
      muF X (x0F X) (proj X hj κ ⁻¹' N) = 0)
    (F : Set (Tau × Fin j × Fin (r - j) → ℂ)) (hF : IsFD (gammaU X hj κ) F) :
    ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧
      IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  obtain ⟨hFm, hFD, hcov, hbad⟩ := hF
  obtain ⟨N0, hN0, hN0m, hN0z⟩ := exists_measurable_superset_of_null hbad
  have ho := isOrth_x0F X
  have hOm : MeasurableSet (OmF X (x0F X)) :=
    ((FourierCoefficientDomain.isOpen_dom X).preimage (KU.cont_cpt X (x0F X))).measurableSet
  have hNm : MeasurableSet (F ∩ N0) := hFm.inter hN0m
  have hNz : muD Tau j (r - j) (F ∩ N0) = 0 := measure_mono_null Set.inter_subset_right hN0z
  refine ⟨F \ N0, hFm.diff hN0m, Set.sdiff_subset, ?_, ?_, Set.inter_subset_right, ?_, ?_⟩
  · rw [Set.sdiff_sdiff_right_self]; exact hNz
  · exact (measurable_proj X hj κ (hFm.diff hN0m)).inter hOm
  · rintro z ⟨⟨hz, hzN⟩, hzO⟩ z' ⟨⟨hz', -⟩, -⟩ γ hγ b hb h
    have hd : domPt X hj κ (cpt X (x0F X) z') = domPt X hj κ (lact γ (cpt X (x0F X) z)) := by
      rw [h, KU.lact_rmul', domPt_rmul X hj κ hb]
    have hfix : domPt X hj κ (lact γ (cpt X (x0F X) z)) = domPt X hj κ (cpt X (x0F X) z) := by
      by_contra hne
      apply hzN
      apply hN0
      refine ⟨hz, toUpq X hj κ γ, ⟨γ, hγ, rfl⟩, ?_, ?_⟩
      · change flat (moebI _ (domPt X hj κ (cpt X (x0F X) z))) ∈ F
        rw [← domPt_lact X hj κ hp γ hzO, ← hd]
        exact hz'
      · change moebI _ (domPt X hj κ (cpt X (x0F X) z)) ≠ domPt X hj κ (cpt X (x0F X) z)
        rw [← domPt_lact X hj κ hp γ hzO]
        exact hne
    have h1 := hfree γ hγ _ hzO hfix
    rw [h1, KU.lact_one] at h
    have hS : cpt X (x0F X) z' ∈ KU.Sset X (x0F X) {z} := by
      rw [h, KU.rmul_mem_S X hb, KU.cpt_mem_S X ho]
      rfl
    exact ((KU.cpt_mem_S X ho z').1 hS).symm
  · have := KU.countable_Γ X
    have hA : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (fun x => flat (domPt X hj κ x)) ⁻¹' (F ∩ N0) := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (measurable_domPt X hj κ hNm) ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_preimage, domPt_rmul X hj κ hb]
      · exact measure_eq_zero_iff_ae_notMem.1
          (hnull _ hNm (Set.inter_subset_left.trans hFD) hNz)
    have hB : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (KU.Sset X (x0F X) (OmF X (x0F X)))ᶜ := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (KU.meas_S X ho hOm).compl ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_compl_iff, KU.rmul_mem_S X hb]
      · filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hz hn
        exact hn ((KU.cpt_mem_S X ho z).2 hz)
    filter_upwards [hA, hB, ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hzA hzB hzO
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγF⟩ := hcov _ (domPt_mem X hj κ hp hzO)
    rw [← domPt_lact X hj κ hp γ hzO] at hγF
    have h1 := hzA ⟨γ, hγ⟩
    obtain ⟨⟨z', b⟩, ⟨hz', hb⟩, he⟩ := not_not.1 (hzB ⟨γ, hγ⟩)
    have he' : rmul (cpt X (x0F X) z') b = lact γ (cpt X (x0F X) z) := he
    have hpr : proj X hj κ z' = flat (domPt X hj κ (lact γ (cpt X (x0F X) z))) := by
      rw [← he', domPt_rmul X hj κ hb]; rfl
    refine ⟨z', ⟨?_, hz'⟩, γ⁻¹, X.Γ.inv_mem hγ, b, hb, ?_⟩
    · rw [Set.mem_preimage, hpr]
      exact ⟨hγF, fun hn => h1 ⟨hγF, hn⟩⟩
    · rw [he', KU.lact_lact, inv_mul_cancel, KU.lact_one]

end GlobalTheory.FlagFibre.FundPre
end

