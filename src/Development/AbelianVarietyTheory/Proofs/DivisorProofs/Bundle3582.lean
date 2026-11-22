import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3575
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3517
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualRepresentableAffineBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem hasRep_affine : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  intro R _ A _ g hA hg
  obtain ⟨S, B, _, φ, -, hS, hB, hgB, hφ⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g A ∅ hA hg
  have h₀ : HasRep B g (𝟙_ _) := GlobalTheory.T.hasProperSmoothDualRepresentative_finiteType S B g hB hgB
  exact (GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ _ B A φ hφ g (𝟙_ _)).1.2 (GlobalTheory.T.baseChangeBis _ B _ _ g (toUnit _) h₀)

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisation
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.AbVarDieu

variable {p : ℕ} [Fact p.Prime]

theorem pow_comp_hom {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_eq_ppow_smul (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B : AbVar k} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B)
    (n : ℕ) (h : ∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') : ∃ f' : A ⟶ B, f = p ^ n • f' := by
  obtain ⟨g, hg⟩ := (GlobalTheory.T.dieudonne_integrality_and_faithful p T k G H (t.map t' f.hom)).1 n h
  exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A B G H t t' f).1 n g hg

theorem map_nsmul_id {k : Type} [Field k] {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X) (N : ℕ) :
    t.map t ((N • 𝟙 A : A ⟶ A).hom) = (N : ℤ_[p]) • 𝟙 G := by
  have : IsMonHom (𝟙 A.X ^ N) := inferInstanceAs (IsMonHom ((N • 𝟙 A : A ⟶ A).hom))
  exact t.map_pow_id N

theorem tmap_comp (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H K : PDivGroup p k}
    (f : G ⟶ H) (g : H ⟶ K) (y : T.M K) : T.map (f ≫ g) y = T.map f (T.map g y) := by
  have := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H K trivial trivial trivial).2.1 f g
  exact LinearMap.congr_fun this y

theorem tmap_ppow_smul_id (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {H : PDivGroup p k}
    (a : ℕ) (y : T.M H) : T.map ((p : ℤ_[p]) ^ a • 𝟙 H) y = p ^ a • y := by
  have h := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k H H H trivial trivial trivial
  have h5 := h.2.2.2.2.1 a (𝟙 H) y
  have h1 := h.1
  change T.base.map trivial trivial _ y = _
  rw [h5, h1]
  rfl

theorem exists_ppow_quasiInverse {k : Type} [Field k] [CharP k p] {A B : AbVar k} (f : A ⟶ B)
    (hf : IsIsogeny f) (e : ℕ) (hdeg : deg f = p ^ e) :
    ∃ (a : ℕ) (f₁ : B ⟶ A), f ≫ f₁ = p ^ a • 𝟙 A ∧ f₁ ≫ f = p ^ a • 𝟙 B := by
  obtain ⟨N, f', hN, -, e1, e2⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p (Fact.out : p.Prime).ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hpm (dvd_zero p))
  have hmk : (m : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hcop : Nat.Coprime m (deg f) := by
    rw [hdeg]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm).symm
  obtain ⟨f₁, hf₁⟩ := exists_nsmul_eq_of_kills_torsion k B A f' m hmk (fun y hy => by
    apply GlobalTheory.AV.KerInv.eq_one_of_coprime f hf m hm0 hcop (y ≫ f'.hom)
    · rw [Category.assoc, ← comp_hom, e2, nsmul_hom, id_hom, comp_id_pow_eq, pow_mul', hy, one_pow]
    · rw [← pow_comp_hom, hy, MonObj.one_comp])
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm0.ne'
  refine ⟨a, f₁, ?_, ?_⟩
  · refine sub_eq_zero.1 (hom_torsionFree k A A (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hf₁, e1, smul_smul, mul_comm]
    exact sub_self _
  · refine sub_eq_zero.1 (hom_torsionFree k B B (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.nsmul_comp, ← hf₁, e2, smul_smul, mul_comm]
    exact sub_self _

theorem exists_factor_of_range_le (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B C : AbVar k} {G H K : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X)
    (t'' : K.TorsionTower C.X) (f : A ⟶ B) (g : A ⟶ C) (e : ℕ) (hf : IsIsogeny f) (hdeg : deg f = p ^ e)
    (hr : LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom))) :
    ∃ u : B ⟶ C, f ≫ u = g := by
  obtain ⟨a, f₁, h1, h2⟩ := exists_ppow_quasiInverse f hf e hdeg
  have hdiv : ∀ x, ∃ x', T.map (t'.map t'' (f₁ ≫ g).hom) x = p ^ a • x' := by
    intro x
    obtain ⟨y, hy⟩ := hr (LinearMap.mem_range_self _ x)
    refine ⟨y, ?_⟩
    have c1 : t'.map t'' (f₁ ≫ g).hom = t'.map t f₁.hom ≫ t.map t'' g.hom :=
      (t'.map_congr t'' (comp_hom f₁ g)).trans (t'.map_comp t t'' _ _)
    have c2 : t'.map t f₁.hom ≫ t.map t' f.hom = (p : ℤ_[p]) ^ a • 𝟙 H := by
      rw [← t'.map_comp t t', ← Nat.cast_pow, ← map_nsmul_id t']
      exact t'.map_congr t' ((comp_hom f₁ f).symm.trans (congrArg Hom.hom h2))
    rw [c1, tmap_comp, ← hy, ← tmap_comp, c2, tmap_ppow_smul_id]
  obtain ⟨u, hu⟩ := exists_eq_ppow_smul T t' t'' (f₁ ≫ g) a hdiv
  refine ⟨u, sub_eq_zero.1 (hom_torsionFree k A C ((p ^ a : ℕ) : ℤ) _ (by exact_mod_cast (pow_pos (Fact.out : p.Prime).pos a).ne') ?_)⟩
  rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hu, ← Category.assoc, h1,
    Preadditive.nsmul_comp, Category.id_comp]
  exact sub_self _

theorem abVar_dieudonne_integral_length_factor : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  intro p _ T k _ _ _ A B G H t t' f
  refine ⟨fun n h => exists_eq_ppow_smul T t t' f n h, fun hf => ?_,
    fun C K t'' g e hf hdeg hr => exists_factor_of_range_le T t t' t'' f g e hf hdeg hr⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree p k A B G H t t' f hf
  exact ⟨h1, GlobalTheory.T.dieudonneColength_eq_log_degree p T k G H _ _ h1 h2⟩

end GlobalTheory.Dieu.AbVarDieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatementsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  first | exact @GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | exact GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | (intros; apply GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigBase

theorem grp_through {S S₁ S₂ : Scheme.{0}} {B' : Over S₂} {Q : Over S₁} {D O : Over S} [GrpObj B'] [GrpObj Q]
    [GrpObj D] [GrpObj O] {g : S₂ ⟶ S} {π : B'.left ⟶ Q.left} {β : Q.left ⟶ D.left} {φB : O.left ⟶ D.left}
    {ρ₁ : S₂ ⟶ S₁} {j : S₁ ⟶ S} (hπ : IsGrpPullback B' Q ρ₁ π) (hβ : IsGrpPullback Q D j β)
    (hφ : IsGrpPullback O D (𝟙 S) φB) (hg : ρ₁ ≫ j = g) :
    ∃ π' : B'.left ⟶ O.left, π' ≫ φB = π ≫ β ∧ π' ≫ O.hom = B'.hom ≫ g ∧ IsGrpPullback B' O g π' := by
  have hc := (hπ.comp hβ).congr hg rfl
  have w : (π ≫ β) ≫ D.hom = (B'.hom ≫ g) ≫ 𝟙 S := by rw [Category.comp_id]; exact hc.1.w
  exact ⟨hφ.1.lift (π ≫ β) (B'.hom ≫ g) w, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _,
    hφ.cancel (hc.congr (Category.comp_id g).symm (hφ.1.lift_fst _ _ _).symm) (hφ.1.lift_snd _ _ _)⟩

theorem lb_through {X Y Z T : Scheme.{0}} {L₀ : LB X} {L : LB Y} {M : LB Z} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hM : M.IsLB) {φB : X ⟶ Y} {β : Z ⟶ Y} {π₁ π₂ : T ⟶ Z} {π₁' π₂' : T ⟶ X} (h₀ : LBIso L₀ (L.pull φB))
    (hβ : LBIso M (L.pull β)) (h : LBIso (M.pull π₁) (M.pull π₂)) (e₁ : π₁' ≫ φB = π₁ ≫ β)
    (e₂ : π₂' ≫ φB = π₂ ≫ β) : LBIso (L₀.pull π₁') (L₀.pull π₂') := by
  have key : ∀ {A : Scheme.{0}} {L' : LB A} {F : A ⟶ Y}, LBIso L' (L.pull F) → ∀ j : T ⟶ A,
      LBIso (L'.pull j) (L.pull (j ≫ F)) := fun H j =>
    LBIso.chartPull (chartPullPull _ _) (chartPullSame L _ _ _ j fun _ => rfl) H
  have a₁ := key h₀ π₁'
  have a₂ := key h₀ π₂'
  have b₁ := key hβ π₁
  have b₂ := key hβ π₂
  rw [e₁] at a₁
  rw [e₂] at a₂
  exact LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hL₀ _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hL _)
    (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hM _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hM _) a₁ b₁.symm) h) b₂) a₂.symm

theorem const_on_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C Cn k _ ρ a hC
  obtain ⟨B', _, π₁, π₂, w, c', h₁, h₂, h0, hw, hc', -⟩ := hC
  obtain ⟨g, hD, -, hxe, -⟩ := Cn.data
  haveI := hD.e_hom
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (specOf (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback _ _)).congr (Category.id_comp _) rfl
  have hsp : ∀ ρ' : R →+* DualNumber k, spMap ρ' ≫ specOf (Cn.ψ.comp MvPolynomial.C) = spMap (ρ'.comp (Cn.ψ.comp MvPolynomial.C)) := fun ρ' => by
    rw [← Spec.map_comp]; rfl
  obtain ⟨π₁', e₁, w₁, g₁⟩ := grp_through h₁ hβ Cn.L.ab.1 (hsp ρ)
  obtain ⟨π₂', e₂, w₂, g₂⟩ := grp_through h₂ hβ Cn.L.ab.1
    (hsp _ : _ = spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))))
  have hfst : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (ρ.comp (Cn.ψ.comp MvPolynomial.C)) =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have agree : ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁' = x ≫ π₂' := by
    intro Z x y hx
    apply Cn.L.ab.1.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, e₂, ← Category.assoc, ← Category.assoc, h0 Z x y hx]
    · rw [Category.assoc, Category.assoc, w₁, w₂, ← Category.assoc, ← Category.assoc, hx, Category.assoc,
        Category.assoc, hfst]
  obtain ⟨w₀, hw₀⟩ := Cn.L.ab.2.2
  have hLB : LBIso (Cn.L.o.t.PP.L.pull π₁') (Cn.L.o.t.PP.L.pull π₂') :=
    lb_through Cn.L.o.t.PP.isLB Cn.L.D.P.isLB C.P.D.toPre.P.isLB ⟨w₀, hw₀⟩ ⟨hD.w, hD.w_gen⟩ ⟨w, hw⟩ e₁ e₂
  obtain ⟨o', m₁, m₂, io, hio, hm₁, hm₂⟩ :=
    GlobalTheory.T.exists_objectMaps_of_dualNumber_identifications c Cn.L.W Cn.L.b Cn.L.o k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) B' π₁' π₂' g₁ g₂ agree hLB
  have hn : ((l.M' : ℕ) : k) ≠ 0 := by
    intro h0'
    have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    have hk : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ((ρ.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b))
        (l.M' : c.F) = 0 := by rw [map_natCast]; exact h0'
    rw [map_eq_zero_iff _ (RingHom.injective _)] at hk
    exact hM (by exact_mod_cast hk)
  have agree' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ := by
    intro Z x y hx
    rw [hm₁, hm₂, ← Category.assoc, ← Category.assoc]
    exact agree Z _ y (by rw [Category.assoc, hio, hx])
  have hinv : io.inv ≫ o'.t.G.hom = B'.hom := by rw [← hio, Iso.inv_hom_id_assoc]
  have hc : ∀ y, (C.P.D.toPre.c (Cn.e.symm y)).left ≫ hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) =
      specOf (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • y)).left := fun y => by
    have := hD.c_pr (Cn.e.symm y)
    rw [hxe, LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨x, hx₁, hx₂, hx₀⟩ := GlobalTheory.T.dualNumber_points_pulledBack_object_from_base Cn.L k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ l.M' hn agree'
    (fun y => c' (Cn.e.symm y) ≫ io.inv)
    (fun y => by rw [Category.assoc, hinv, (hc' _).1])
    (fun y => by
      rw [hm₁]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₁, ← Category.assoc, (hc' _).2.1, Category.assoc, hc,
        ← Category.assoc, hsp])
    (fun y => by
      rw [hm₂]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₂, ← Category.assoc, (hc' _).2.2, Category.assoc, hc,
        ← Category.assoc, hsp]; rfl)
  exact Cn.L.fineEps k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ x hx₁ hx₂ hx₀

end GlobalTheory.RigBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalChartResidueFieldDimensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalChart_residueField_dimension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → ((residue (ChartRing k m e)).comp C.b).EssFiniteType ∧ (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra; ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim) := by
  first | exact @GlobalTheory.UCanon.canon_residue_dim | exact GlobalTheory.UCanon.canon_residue_dim | (intros; apply GlobalTheory.UCanon.canon_residue_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.canon_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn
  obtain ⟨ε', τ₀, hε', hFB, hTau⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  refine ⟨Cn.N, fun k => Cn.ψ (MvPolynomial.X k), ε', τ₀, fun i => Cn.bd i, ?_, fun k => Cn.tor k, hTau, ?_⟩
  · intro i
    rw [hε', Cn.cone i]
  · intro K _ _ ev k₀ hk₀ hemb hsep
    obtain ⟨h1, h2, h3⟩ := hsep
    have hbase : ∀ a, ev ((Cn.ψ.comp MvPolynomial.C) a) ∈ k₀ :=
      GlobalTheory.T.canonicalFamily_base_value_mem_descended_point Cn.L C.P.D.toPre C.P.oD (Cn.ψ.comp MvPolynomial.C) (fun k => Cn.ψ (MvPolynomial.X k))
        (fun k => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) Cn.e Cn.data K ev k₀ hk₀ h2
    have htor := h3 Cn.L.W (Cn.ψ.comp MvPolynomial.C) hFB hbase
    have hX : ∀ k, ev (Cn.ψ (MvPolynomial.X k)) ∈ k₀ := by
      rintro (i | i)
      · have := h1 i
        simp only at this
        rw [this]; exact k₀.zero_mem
      · exact htor i
    have hall : ∀ a : MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W, ev (Cn.ψ a) ∈ k₀ := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C a => exact hbase a
      | add p q hp hq => rw [map_add, map_add]; exact k₀.add_mem hp hq
      | mul_X p k hp => rw [map_mul, map_mul]; exact k₀.mul_mem hp (hX k)
    have hft : ((MvPolynomial.C : Cn.L.W →+* MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W).comp Cn.L.b).EssFiniteType := by
      refine RingHom.EssFiniteType.comp Cn.L.ft ?_
      exact (RingHom.FiniteType.essFiniteType (by
        rw [← MvPolynomial.algebraMap_eq]
        exact RingHom.finiteType_algebraMap.mpr inferInstance))
    exact GlobalTheory.T.closedPoint_of_values_in_small_algClosed c.F (MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W) R K (MvPolynomial.C.comp Cn.L.b) hft Cn.ψ Cn.compl
      ev k₀ hemb hall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesModStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod | exact GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod | (intros; apply GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqMinpolyPow
section
open CategoryTheory Polynomial
open GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.CharpolyMinpolyPower

theorem eq_pow_of_roots (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (P m : ℚ[X]) (hP : P.Monic)
    (hm : m.Monic) (hirr : Irreducible m) (h : ∀ a : Ω, aeval a P = 0 → minpoly ℚ a = m) :
    ∃ k : ℕ, P = m ^ k := by
  suffices H : ∀ n : ℕ, ∀ Q : ℚ[X], Q.natDegree = n → Q.Monic →
      (∀ a : Ω, aeval a Q = 0 → minpoly ℚ a = m) → ∃ k : ℕ, Q = m ^ k from H _ P rfl hP h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hQn hQ hroots
    by_cases hn : Q.natDegree = 0
    · exact ⟨0, by rw [pow_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hQ hn⟩
    · have hdeg : Q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hQ.ne_zero]
        exact_mod_cast hn
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero Ω Q hdeg
      have hdvd : m ∣ Q := hroots a ha ▸ minpoly.dvd ℚ a ha
      obtain ⟨Q', rfl⟩ := hdvd
      have hQ' : Q'.Monic := hm.of_mul_monic_left hQ
      have hsum : (m * Q').natDegree = m.natDegree + Q'.natDegree := hm.natDegree_mul hQ'
      have hm0 : 0 < m.natDegree := hirr.natDegree_pos
      obtain ⟨k, hk⟩ := ih Q'.natDegree (by omega) Q' rfl hQ'
        (fun b hb => hroots b (by rw [map_mul, hb, mul_zero]))
      exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩

theorem deg_ne_zero {K : Type} [Field K] (A : AbVar K) {F : Type} [Field F] [NumberField F]
    (ι : NumberField.RingOfIntegers F →+* End A) (r : NumberField.RingOfIntegers F) (hr : r ≠ 0) :
    deg (A := A) (B := A) (ι r) ≠ 0 := by
  have hI : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hN0 : Ideal.absNorm (Ideal.span {r}) ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
  have hc : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hN0
  have hι : ι r ≫ ι s = ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • 𝟙 A := by
    rw [← End.mul_def, ← map_mul, hs, map_natCast, natCast_zsmul]
    exact (nsmul_one (A := End A) _).symm
  obtain ⟨-, hdN⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A _ hc
  have hcomp := (isIsogeny_comp_iff_and_deg_comp K A A A (ι r) (ι s) rfl rfl).2
  rw [hι, hdN] at hcomp
  intro h0
  rw [h0, zero_mul] at hcomp
  exact pow_ne_zero _ (Int.natAbs_ne_zero.2 hc) hcomp

theorem charpoly_eq_minpoly_pow {K : Type} [Field K] (A : AbVar K) (hA : A.dim ≠ 0) {F : Type} [Field F]
    [NumberField F] (ι : NumberField.RingOfIntegers F →+* End A) (x : NumberField.RingOfIntegers F) :
    ∃ k : ℕ, 0 < k ∧ (charpoly (ι x)).map (Int.castRingHom ℚ) = minpoly ℚ (x : F) ^ k := by
  obtain ⟨hcp, -⟩ := charpoly_spec K A (ι x)
  obtain ⟨hmon, hdeg, -⟩ := hcp
  have hPm : ((charpoly (ι x)).map (Int.castRingHom ℚ)).Monic := hmon.map _
  have hPdeg : ((charpoly (ι x)).map (Int.castRingHom ℚ)).natDegree = 2 * A.dim := by
    rw [hmon.natDegree_map, hdeg]
  let ιa : NumberField.RingOfIntegers F →ₐ[ℤ] End A :=
    AlgHom.mk ι (fun n => by
      show ι (algebraMap ℤ _ n) = algebraMap ℤ (End A) n
      rw [eq_intCast (algebraMap ℤ (NumberField.RingOfIntegers F)), eq_intCast (algebraMap ℤ (End A))]
      exact map_intCast ι n)
  have hxint : IsIntegral ℚ (x : F) := Algebra.IsIntegral.isIntegral _
  have key : ∀ a : AlgebraicClosure ℚ, aeval a ((charpoly (ι x)).map (Int.castRingHom ℚ)) = 0 →
      minpoly ℚ a = minpoly ℚ (x : F) := by
    intro a ha
    have haint : IsIntegral ℚ a := IsAlgebraic.isIntegral ⟨_, hPm.ne_zero, ha⟩
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ a)
    have hRa : aeval a (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 :=
      IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) _ (minpoly.aeval ℚ a)
    have hprod := deg_aeval_eq_prod_aroots K A (ι x) (AlgebraicClosure ℚ)
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))
    have hmem : a ∈ ((charpoly (ι x)).map (Int.castRingHom ℚ)).aroots (AlgebraicClosure ℚ) :=
      (Polynomial.mem_aroots).2 ⟨hPm.ne_zero, ha⟩
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, hmem, hRa⟩)] at hprod
    have hdeg0 : deg (A := A) (B := A) (aeval (ι x)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))) = 0 := by
      have h := (map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).1 hprod
      exact_mod_cast h
    rw [show aeval (ι x) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) =
        ι (aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))) from
      Polynomial.aeval_algHom_apply ιa x _] at hdeg0
    have hRx : aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      by_contra hne
      exact deg_ne_zero A ι _ hne hdeg0
    have hRxF : aeval (x : F) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      have h := congrArg (algebraMap (NumberField.RingOfIntegers F) F) hRx
      rwa [map_zero, ← Polynomial.aeval_algebraMap_apply] at h
    have hqx : aeval (x : F) (minpoly ℚ a) = 0 := by
      have h1 : aeval (x : F) ((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
          (minpoly ℚ a)).map (algebraMap ℤ ℚ)) = 0 := by
        rwa [Polynomial.aeval_map_algebraMap]
      rw [hb, map_zsmul] at h1
      exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero hbM)
    exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hqx (minpoly.monic haint)
  obtain ⟨k, hk⟩ := eq_pow_of_roots (AlgebraicClosure ℚ) _ _ hPm (minpoly.monic hxint)
    (minpoly.irreducible hxint) key
  refine ⟨k, Nat.pos_of_ne_zero ?_, hk⟩
  rintro rfl
  rw [hk, pow_zero, Polynomial.natDegree_one] at hPdeg
  omega

end GlobalTheory.CharpolyMinpolyPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetrizedBundleNefAntitone
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

noncomputable section

namespace GlobalTheory.HtNefCore

theorem exists_cover_nefOver : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  intro h2 hH D O hc hf A T H hr c Q l hl hlp
  obtain ⟨V, M, hM, hA⟩ := GlobalTheory.T.adelic_norm_nef_partial_sums h2 hH D O hc hf A T H hr c Q l hl hlp
  refine ⟨V, M, hM, fun n hn => ?_⟩
  have hB := GlobalTheory.T.adelic_norm_nef_indicators h2 hH D O hc hf A T H hr c Q l hl hlp V M hM
  exact GlobalTheory.T.nef_combination_of_partial_indicators V.ar D.what₂.Tau O.N M l (fun τ i hi => by convert hA τ i hi) (fun τ => by convert hB τ using 3) n hn

end GlobalTheory.HtNefCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_global_forms_base_change : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  first | exact @GlobalTheory.AbCoh.baseChange_HH1_globForm | exact GlobalTheory.AbCoh.baseChange_HH1_globForm | (intros; apply GlobalTheory.AbCoh.baseChange_HH1_globForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamH1RankPrimitiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_h1_rank_primitive : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (HH1 A.hom) (2 * g) ∧ DeRhamH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.rank_prim_HH1 | exact GlobalTheory.AbCoh.rank_prim_HH1 | (intros; apply GlobalTheory.AbCoh.rank_prim_HH1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdArootsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_aeval_end_eq_prod_aroots : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ), algebraMap ℚ Ω (deg (A := A) (B := A) (Polynomial.aeval f R) : ℚ) = ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map (fun a => Polynomial.aeval a R)).prod := by
  first | exact @GlobalTheory.AV.AbVar.deg_aeval_eq_prod_aroots | exact GlobalTheory.AV.AbVar.deg_aeval_eq_prod_aroots | (intros; apply GlobalTheory.AV.AbVar.deg_aeval_eq_prod_aroots <;> assumption)
end

