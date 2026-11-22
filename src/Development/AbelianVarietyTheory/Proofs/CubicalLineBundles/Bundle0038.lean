import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.TripleModel

section Tensor

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X Y : Over S} {X' Y' : Over S'}

theorem isPullback_tensor {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left} (ha : IsPullback a X'.hom X.hom f)
    (hb : IsPullback b Y'.hom Y.hom f) {c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left}
    (h₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (h₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have h : IsPullback (fst X' Y').left (snd X' Y').left X'.hom Y'.hom := .of_hasPullback _ _
  have h₀ : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := .of_hasPullback _ _
  have h₃ : IsPullback c (snd X' Y').left (snd X Y).left b := by
    refine IsPullback.of_right ?_ h₂ h₀
    rw [h₁, hb.w]
    exact h.paste_horiz ha
  rw [← Over.w (snd X' Y'), ← Over.w (snd X Y)]
  exact h₃.paste_vert hb

end Tensor

section Cube

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {M : LB G.left} {M' : LB G'.left}

theorem lbIso_cube_pull (h : IsGrpPullback G' G f φ) (hM : M.IsLB) (hM' : M'.IsLB) (e : LBIso (M.pull φ) M')
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' M') := by
  have hc : (cubeLB G x M).IsLB := DVR.linComb_isLB _ hM _ _
  have h₁ : LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' (M.pull φ)) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ U.left rfl)
      (chartPullLinComb M _ _ _ _ U.left fun I => psum_push h _ _ U hx I.down) (PolBaseChange.lbIso_refl hc)
  exact LBIso.trans (pull_isLB hc _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (DVR.linComb_isLB _ hM' _ _) h₁
    (PowPrimitive.lbIso_linComb e _ _)

theorem lbIso_cube_of_eq (hM : M.IsLB) {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x y : Fin n → (T ⟶ G))
    (h : ∀ i, ρ ≫ x i = ρ ≫ y i) : LBIso ((cubeLB G x M).pull ρ.left) ((cubeLB G y M).pull ρ.left) :=
  LBIso.chartPull (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ x (fun i => ρ ≫ x i) (fun _ => rfl) I.down)
    (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ y (fun i => ρ ≫ x i) h I.down)
    (PolBaseChange.lbIso_refl (L := cubeLB G (fun i => ρ ≫ x i) M) (DVR.linComb_isLB _ hM _ _))

theorem exists_gen_theta_zero (hM : M.IsLB) :
    ∃ t : LB.Gen ((Theta G M).pull (eSec (G ⊗ G ⊗ G))), t.IsGen := by
  have e : η[G ⊗ G ⊗ G] = lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G)) := by
    ext <;> simp [Hom.one_def]
  obtain ⟨t, ht⟩ := (PrimNorm.hasGen_iff hM
    (fun I : thK => (lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G))).left ≫ thφ G (x3 G) I) thε).2
    ((prod_cub _ _ _ (PrimNorm.cls M)).trans (by simp))
  exact gen_chartPull (chartPullOut M (thφ G (x3 G)) thε (eSec (G ⊗ G ⊗ G)) _ fun I => by rw [eSec, e]) t ht

end Cube

theorem exists_gen_of_lbIso {X : Scheme.{0}} {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

theorem exists_triple_of_abelian_model : Out.Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (B : Over (Sp R)) [GrpObj B] (φ : t₀.G.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback t₀.G B (spMap (algebraMap R K)) φ → ∃ (t : SAB H (Sp R)) (m : SABMap t₀ t (spMap (algebraMap R K))) (e : t.G ≅ B), IsMonHom e.hom ∧ m.φ ≫ e.hom.left = φ := by
  intro hL hext E _ _ _ H R K _ _ _ _ _ t₀ B _ φ hB h
  have := hB.comm
  have hB₂ := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
  have hB₃ := AbelianSchemeGerms.isAbelianScheme_tensor B _ hB hB₂
  obtain ⟨act, hact⟩ := exists_oAct_extend_dedekind hext R K (𝓞 E) B t₀.G φ hB h t₀.act
  obtain ⟨M, hM⟩ := exists_rigLB_extension_dedekind R K B hB _ φ t₀.G.hom h.1 t₀.PP.L t₀.PP.isLB
  have lb : ∀ {T : Over (Sp R)} {n : ℕ} (x : Fin n → (T ⟶ B)) {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have lb₀ : ∀ {T : Over (Sp K)} {n : ℕ} (x : Fin n → (T ⟶ t₀.G)), (cubeLB t₀.G x t₀.PP.L).IsLB :=
    fun x => DVR.linComb_isLB _ t₀.PP.isLB _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ t₀.G) a,
      pushPt h.1.w (x ≫ t₀.act.act a) = pushPt h.1.w x ≫ act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  let U₂ := lift (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))
  have p₂ : IsPullback U₂.left (t₀.G ⊗ t₀.G).hom (B ⊗ B).hom (spMap (algebraMap R K)) :=
    isPullback_tensor h.1 h.1
      (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
      (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
  let U₃ := lift (pushPt h.1.w (x3 t₀.G 0)) (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))
  have p₃ : IsPullback U₃.left (t₀.G ⊗ t₀.G ⊗ t₀.G).hom (B ⊗ B ⊗ B).hom (spMap (algebraMap R K)) := by
    refine isPullback_tensor h.1 p₂ (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))))
      ((congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2))))).trans ?_)
    apply pullback.hom_ext
    · refine (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_fst
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
    · refine (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_snd
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
  have hT : ∃ t : LB.Gen (Theta B M.L), t.IsGen :=
    TrivDedekind.exists_gen_of_generic R K (B ⊗ B ⊗ B) hB₃ _ U₃.left _ p₃ (Theta B M.L) (lb _ M.isLB) (exists_gen_theta_zero M.isLB)
      (exists_gen_of_lbIso (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM (x3 t₀.G) (x3 B) U₃
          (fun i => by fin_cases i <;> simp [U₃, x3])).symm ⟨t₀.cub.t, t₀.cub.isGen⟩)
  have ha : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M.L)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M.L) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    refine IsoDescent.lbIso_of_field R K (algebraMap R K) (IsFractionRing.injective R K) (B ⊗ B) hB₂ _ U₂.left _ p₂ _ _
      (lb _ M.isLB) (lb _ M.isLB) (lbIso_cube_of_eq M.isLB η[B ⊗ B] _ _ fun i => ?_) ?_
    · fin_cases i <;> simp
    · refine LBIso.trans (pull_isLB (lb _ M.isLB) _) (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_)
        (LBIso.trans (lb₀ _) (lb₀ _) (pull_isLB (lb _ M.isLB) _) (t₀.adj a)
          (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂]
      · fin_cases i
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂])
  obtain ⟨PP, cub, sym, hPP, -, prim, adj⟩ :=
    PrimNorm.exists_primitive_normalisation hL.globalFns E H _ B act M.L hB M.isLB hT ha
  let t : SAB H (Sp R) := ⟨B, isSemiAbelian_of_isAbelianScheme B hB, act, PP, cub, sym, adj, prim⟩
  have hφ : LBIso t₀.PP.L (PP.L.pull φ) := by
    let U := pushPt h.1.w (𝟙 t₀.G)
    have eU : U.left = φ := Category.id_comp _
    have h₁ : LBIso ((cubeLB B ![𝟙 B, act.act H.w0] M.L).pull U.left)
        (cubeLB t₀.G ![𝟙 t₀.G, t₀.act.act H.w0] t₀.PP.L) := by
      refine lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U fun i => ?_
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    rw [eU] at h₁
    exact LBIso.trans t₀.PP.isLB (lb₀ _) (pull_isLB PP.isLB _) t₀.prim
      (LBIso.trans (lb₀ _) (pull_isLB (lb _ M.isLB) _) (pull_isLB PP.isLB _) h₁.symm
        (PowPrimitive.lbIso_linComb hPP.symm _ _))
  obtain ⟨m, hm⟩ := CartTriple.exists_tripleMap hL.globalFns E H _ _ _ t₀ t φ (PolPull.isAbelianScheme_of_isGrpPullback hB h) h hact hφ
  exact ⟨t, m, Iso.refl B, inferInstanceAs (IsMonHom (𝟙 B)), (Category.comp_id _).trans hm⟩

end GlobalTheory.CM.TripleModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def kFun {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H

theorem kFun_coe {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : ((kFun D ε x y : OK H) : 𝓞 E) =
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : 𝓞 E) + (((ε : ℤ) * D.EF x y : ℤ) : 𝓞 E) * H.w0 := by
  simp only [kFun, wK, Subalgebra.coe_add, Subalgebra.coe_mul, SubringClass.coe_intCast]

theorem kform_w0_sq (H : Host E) : H.w0 * H.w0 = H.w0 - (((1 + H.d) / 4 : ℕ) : 𝓞 E) := by
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.2.1
  simp only [wK, Subalgebra.coe_add, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h
  linear_combination h

theorem kform_bar_w0 (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  obtain ⟨br, h1, h2, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.1
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) h2
  simp only [Subalgebra.coe_add, h1, Subalgebra.coe_one] at h
  simp only [wK] at h
  linear_combination h

theorem kform_skew {H : Host E} (D : Datum H) (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt] at h
  linarith

theorem kFun_add_left {H : Host E} (D : Datum H) (ε : ℤˣ) (x x' y : D.La) :
    kFun D ε (x + x') y = kFun D ε x y + kFun D ε x' y := by
  simp only [kFun, smul_add, map_add, LinearMap.add_apply]
  push_cast; ring

theorem kFun_add_right {H : Host E} (D : Datum H) (ε : ℤˣ) (x y y' : D.La) :
    kFun D ε x (y + y') = kFun D ε x y + kFun D ε x y' := by
  simp only [kFun, map_add]
  push_cast; ring

theorem kFun_zsmul {H : Host E} (D : Datum H) (ε : ℤˣ) (m : ℤ) (x y : D.La) :
    kFun D ε (m • x) y = (m : OK H) * kFun D ε x y := by
  simp only [kFun, smul_comm H.w0 m x, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast; ring

theorem kFun_w0 {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) :
    kFun D ε (H.w0 • x) y = wK H * kFun D ε x y := by
  apply Subtype.ext
  have hw : H.w0 • H.w0 • x = H.w0 • x - (((1 + H.d) / 4 : ℕ) : ℤ) • x := by
    rw [smul_smul, kform_w0_sq, sub_smul, Nat.cast_smul_eq_nsmul, natCast_zsmul]
  have h2 := kform_w0_sq H
  rw [Subalgebra.coe_mul, kFun_coe, kFun_coe, hw]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, wK]
  generalize ((1 + H.d) / 4 : ℕ) = N at *
  push_cast
  linear_combination (-((ε : ℤ) : 𝓞 E) * (D.EF x y : 𝓞 E)) * h2

theorem kFun_smul {H : Host E} (D : Datum H) (ε : ℤˣ) (a : OK H) (x y : D.La) :
    kFun D ε (a • x) y = a * kFun D ε x y := by
  obtain ⟨⟨m, n⟩, rfl, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 a
  have : ((m : OK H) + (n : OK H) * wK H) • x = m • x + n • H.w0 • x := by
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; rfl
  simp only
  rw [this, kFun_add_left, kFun_zsmul, kFun_zsmul, kFun_w0]; ring

def kLin {H : Host E} (D : Datum H) (ε : ℤˣ) : D.La →ₗ[OK H] D.La →+ OK H where
  toFun x := AddMonoidHom.mk' (kFun D ε x) (kFun_add_right D ε x)
  map_add' x x' := by ext1 y; exact kFun_add_left D ε x x' y
  map_smul' a x := by ext1 y; exact kFun_smul D ε a x y

theorem kLin_apply {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : kLin D ε x y = kFun D ε x y := rfl

theorem kform_coeff_unique (H : Host E) {a b c d : ℤ}
    (h : (a : OK H) + (b : OK H) * wK H = (c : OK H) + (d : OK H) * wK H) : a = c ∧ b = d := by
  have := ((GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 ((a : OK H) + (b : OK H) * wK H)).unique (y₁ := (a, b)) (y₂ := (c, d)) rfl h
  exact Prod.mk.inj this

theorem kLin_perfect {H : Host E} (D : Datum H) (ε : ℤˣ) (f : D.La →ₗ[OK H] OK H) :
    ∃! y, ∀ x, f x = kLin D ε x y := by
  have hε : (ε : ℤ) * ε = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  choose c hc using fun a => ((GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 a).exists
  let b : D.La →+ ℤ := AddMonoidHom.mk' (fun x => -(ε : ℤ) * (c (f x)).2) (by
    intro x x'
    have : (((c (f (x + x'))).1 : ℤ) : OK H) + ((c (f (x + x'))).2 : OK H) * wK H =
        (((c (f x)).1 + (c (f x')).1 : ℤ) : OK H) + (((c (f x)).2 + (c (f x')).2 : ℤ) : OK H) * wK H := by
      rw [← hc, map_add]
      have h1 := hc (f x)
      have h2 := hc (f x')
      push_cast
      linear_combination h1 + h2
    rw [(kform_coeff_unique H this).2]; ring)
  obtain ⟨y, hy⟩ := D.unimod.2 b.toIntLinearMap
  have hb : ∀ x, (ε : ℤ) * D.EF x y = (c (f x)).2 := by
    intro x
    rw [kform_skew, hy]
    change (ε : ℤ) * -(-(ε : ℤ) * (c (f x)).2) = _
    linear_combination (c (f x)).2 * hε
  have hint : ∀ x, ∃ m : ℤ, f x - kFun D ε x y = m := by
    intro x
    refine ⟨(c (f x)).1 - (ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y), ?_⟩
    have h1 := hc (f x)
    rw [kFun, hb]
    push_cast
    linear_combination h1
  refine ⟨y, fun x => ?_, fun y' hy' => ?_⟩
  · obtain ⟨m, hm⟩ := hint x
    obtain ⟨m', hm'⟩ := hint (wK H • x)
    rw [map_smul, kFun_smul, smul_eq_mul, ← mul_sub, hm] at hm'
    have : ((0 : ℤ) : OK H) + (m : OK H) * wK H = (m' : OK H) + ((0 : ℤ) : OK H) * wK H := by
      push_cast; linear_combination hm'
    rw [(kform_coeff_unique H this).2] at hm
    rw [kLin_apply, ← sub_eq_zero, hm, Int.cast_zero]
  · apply D.unimod.1
    ext x
    have h1 := (hc (f x)).symm.trans (hy' x)
    have h2 := (kform_coeff_unique H h1).2
    rw [kform_skew D x y', kform_skew D x y]
    have h3 := hb x
    linear_combination (ε : ℤ) * (h2 + h3) + (D.EF x y' - D.EF x y) * hε

theorem exists_kForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ), ∃ h : D.La →ₗ[OK H] D.La →+ OK H, IsKForm D ε (fun x y => h x y) ∧ (∀ h' : D.La → D.La → OK H, IsKForm D ε h' → h' = fun x y => h x y) ∧ (∀ x y, ((h y x : OK H) : 𝓞 E) = H.bar (h x y : OK H)) ∧ (∀ (s : 𝓞 E) x y, h (s • x) y = h x (H.bar s • y)) ∧ (∀ x, ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E)) ∧ (∀ f : D.La →ₗ[OK H] OK H, ∃! y, ∀ x, f x = h x y) ∧ ∃ (n : ℕ) (x y : Fin n → D.La), ∀ a, a = ∑ i, h a (y i) • x i := by
  intro E _ _ _ H D ε
  refine ⟨kLin D ε, kFun_coe D ε, fun h' hh => ?_, fun x y => ?_, fun s x y => ?_, fun x => ?_,
    kLin_perfect D ε, ?_⟩
  · funext x y
    exact Subtype.ext ((hh x y).trans (kFun_coe D ε x y).symm)
  · have h1 : D.EF (H.w0 • y) x = D.EF (H.w0 • x) y - D.EF x y := by
      rw [D.adj, kform_bar_w0, sub_smul, one_smul, map_sub, kform_skew D x y, kform_skew D (H.w0 • x) y]
      ring
    rw [kLin_apply, kLin_apply, kFun_coe, kFun_coe, h1, kform_skew D x y, map_add, map_mul, map_intCast,
      map_intCast, kform_bar_w0]
    push_cast; ring
  · rw [kLin_apply, kLin_apply, kFun, kFun, smul_comm H.w0 s x, D.adj, D.adj s]
  · rw [kLin_apply, kFun_coe, D.alt]
    push_cast; ring
  · obtain ⟨h1, h2, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.2.2.2 D.La D.fin D.proj
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (OK H) D.La
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    choose y hy using fun i : Fin n => (kLin_perfect D ε ((LinearMap.proj i).comp s)).exists
    refine ⟨n, fun i => π (Pi.single i 1), y, fun a => ?_⟩
    have ha : π (s a) = a := LinearMap.congr_fun hs a
    conv_lhs => rw [← ha, ← Finset.univ_sum_single (s a), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rfl

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueHomOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem existsUnique_hom_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G G₁ : Over S) (G' G₁' : Over S') [GrpObj G] [GrpObj G'] [GrpObj G₁] [GrpObj G₁'] (φ : G'.left ⟶ G.left) (φ₁ : G₁'.left ⟶ G₁.left), IsGrpPullback G' G f φ → IsGrpPullback G₁' G₁ f φ₁ → ∀ F : G ⟶ G₁, (∃! F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left) ∧ ∀ F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left → IsMonHom F → IsMonHom F' := by
  intro S S' f G G₁ G' G₁' _ _ _ _ φ φ₁ h h₁ F
  refine ⟨⟨Over.homMk (h₁.1.lift (φ ≫ F.left) G'.hom ?_) (h₁.1.lift_snd _ _ _),
    h₁.1.lift_fst _ _ _, fun F' hF' => ?_⟩, fun F' hF' hF => ?_⟩
  · rw [Category.assoc, Over.w F]
    exact h.1.w
  · apply Over.OverMorphism.ext
    apply h₁.1.hom_ext
    · exact hF'.trans (h₁.1.lift_fst _ _ _).symm
    · exact (Over.w F').trans (h₁.1.lift_snd _ _ _).symm
  · refine GlobalTheory.Serre.isMonHom_of_mul_comp _ fun T x y => ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
    obtain ⟨Φ₁, hΦ₁⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G₁ G₁' φ₁ h₁ T
    have key : ∀ z : T ⟶ G', Φ₁ (z ≫ F') = Φ z ≫ F := fun z => by
      apply Over.OverMorphism.ext
      rw [hΦ₁, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc, hF']
    apply Φ₁.injective
    rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem etale_pullback_torsion {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S', ⊤))) :
    Etale ((Over.pullback f).obj (torsion G n)).hom := by
  have hs : Smooth ((Over.pullback f).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom f))
  have he : Etale ((Over.pullback f).map (mulN G n)).left := by
    rw [GrpTangent.pullback_map_mulN]
    exact GrpTangent.etale_mulN _ hn
  have h := ((IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.pullback f)).map
    (Over.forget S')
  have h1 : Etale ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left :=
    MorphismProperty.of_isPullback (P := @Etale) h he
  have h2 : Etale ((Over.pullback f).obj (𝟙_ (Over S))).hom :=
    inferInstanceAs (Etale (pullback.snd (𝟙 S) f))
  have e := Over.w ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  have h3 : Etale (((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left ≫
    ((Over.pullback f).obj (𝟙_ (Over S))).hom) := inferInstance
  rw [e] at h3
  exact h3

theorem etale_pullback_tensor {S S' : Scheme.{0}} (f : S' ⟶ S) (A B : Over S)
    (hA : Etale ((Over.pullback f).obj A).hom) (hB : Etale ((Over.pullback f).obj B).hom) :
    Etale ((Over.pullback f).obj (A ⊗ B)).hom := by
  have h : Etale ((Over.pullback f).obj A ⊗ (Over.pullback f).obj B).hom :=
    inferInstanceAs (Etale (pullback.fst ((Over.pullback f).obj A).hom ((Over.pullback f).obj B).hom ≫
      ((Over.pullback f).obj A).hom))
  rw [← Over.w (Functor.Monoidal.μIso (Over.pullback f) A B).inv]
  have : IsIso (Functor.Monoidal.μIso (Over.pullback f) A B).inv.left :=
    inferInstanceAs (IsIso ((Over.forget S').map (Functor.Monoidal.μIso (Over.pullback f) A B).inv))
  infer_instance

theorem torsion_universal {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 ∧ ∀ (T : Over S) (x : T ⟶ G), x ^ n = 1 → ∃ t : T ⟶ torsion G n, t ≫ torsion.ι G n = x := by
  refine ⟨?_, fun T x hx => ⟨pullback.lift x (toUnit T) ?_, pullback.lift_fst _ _ _⟩⟩
  · rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · rw [GrpTangent.comp_mulN, hx, Hom.one_def]

theorem exists_universal_torsion_pair :
    Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y : Out.PolAV (Sp R)) (k : ℕ), 0 < k → ∃ (T₀ : Over (Sp R)) (x₀ : T₀ ⟶ X.A) (y₀ : T₀ ⟶ Y.A), x₀ ^ k = 1 ∧ y₀ ^ k = 1 ∧ (∀ (T : Over (Sp R)) (x : T ⟶ X.A) (y : T ⟶ Y.A), x ^ k = 1 → y ^ k = 1 → ∃ t : T ⟶ T₀, x = t ≫ x₀ ∧ y = t ≫ y₀) ∧ ∀ a b : Γ(T₀.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T₀), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  intro hL R _ _ _ X Y k hk
  have fin : ∀ P : Out.PolAV (Sp R), IsFinite (torsion P.A k).hom ∧ Flat (torsion P.A k).hom := fun P => by
    obtain ⟨h1, h2, -⟩ := hL.mulN (Sp R) P k hk
    rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
    exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A k) h1,
      MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A k) h2⟩
  haveI : CharZero (FractionRing R) := algebraRat.charZero _
  have hu : IsUnit (k : Γ(Sp (FractionRing R), ⊤)) := by
    have : IsUnit (k : FractionRing R) := (Nat.cast_ne_zero.mpr hk.ne').isUnit
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  have et : ∀ P : Out.PolAV (Sp R),
      Etale ((Over.pullback (spMap (algebraMap R (FractionRing R)))).obj (torsion P.A k)).hom := fun P => by
    have := P.isAb.comm
    have := P.isAb.smooth
    exact etale_pullback_torsion _ P.A hu
  obtain ⟨hX, uX⟩ := torsion_universal X.A k
  obtain ⟨hY, uY⟩ := torsion_universal Y.A k
  refine ⟨torsion X.A k ⊗ torsion Y.A k, fst _ _ ≫ torsion.ι X.A k, snd _ _ ≫ torsion.ι Y.A k, ?_, ?_, ?_, ?_⟩
  · rw [← comp_pow, hX, comp_one]
  · rw [← comp_pow, hY, comp_one]
  · intro T x y hx hy
    obtain ⟨s, hs⟩ := uX T x hx
    obtain ⟨t, ht⟩ := uY T y hy
    exact ⟨lift s t, by rw [lift_fst_assoc, hs], by rw [lift_snd_assoc, ht]⟩
  · obtain ⟨f1, f2⟩ := fin X
    obtain ⟨g1, g2⟩ := fin Y
    refine GlobalTheory.LamF.eq_of_geomPoints R (FractionRing R) _ ?_ ?_ (etale_pullback_tensor _ _ _ (et X) (et Y))
    · exact inferInstanceAs (IsFinite (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))
    · exact inferInstanceAs (Flat (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormEqPiMulHermForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.CM.LieMetric

theorem form_eq_sum_sum {K : Type} [Field K] {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, ∑ i, s (y j) * star (s (x i)) * h.form s (Pi.single i 1) (Pi.single j 1) := by
  rw [form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← h.conj_symm, form_sum_right, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm, _root_.mul_assoc]
  rfl

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin n → ℂ) (X : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ j, a j • X j) (∑ i, b i • X i) = ∑ j, ∑ i, a j * star (b i) * hermForm Hm (X j) (X i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_eq_pi_mul_hermForm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ), IsPolFibre s F.P₀ Q ψ → u.IsAH Hm χ → ∀ (c c' : Fin F.P₀.g → K) (w w' : epsR K ⟶ F.P₀.A) (v v' : epsR ℂ ⟶ Q.A) (W W' : Fin Q.g → ℂ), IsLieComb c F.v w → IsLieComb c' F.v w' → IsVecOver s ψ w v → IsVecOver s ψ w' v' → u.IsDiff W v → u.IsDiff W' v' → h.form s c c' = Real.pi * hermForm Hm W' W := by
  intro hU _ K _ _ P F h H s Q ψ u Hm χ hQ hA c c' w w' v v' W W' hw hw' hv hv' hW hW'
  obtain ⟨Q₀, ψ₀, v₀, u₀, Hm₀, χ₀, W₀, a₀, b₀, c₀, d₀⟩ := H s
  obtain ⟨-, -, -, -, t1, -, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q _ u Hm χ hA
  choose x hx using fun i => (existsUnique_isVecOver hQ.2.1.1 (F.v i)).exists
  have hxt : ∀ i, IsTangent (x i) := fun i => (hx i).isTangent hQ.2.1 (F.basis.1 i)
  choose X hX using fun i => (t1 _ (hxt i)).exists
  have key : ∀ (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (v : epsR ℂ ⟶ Q.A) (W : Fin Q.g → ℂ), IsLieComb c F.v w →
      IsVecOver s ψ w v → u.IsDiff W v → W = ∑ i, s (c i) • X i := fun c w v W hw hv hW => by
    have h1 := (lieComb_baseChange K ℂ s _ _ ψ hQ.2.1 _ F.v w c x v hx hw).1 hv
    have h2 := UnifDifferential.isDiff_prod u (fun i => s (c i) • X i) _
      (fun i => Chart.isTan_scale (s (c i)) ((Chart.isTan_iff _).2 (hxt i)))
      (fun i => UnifDifferential.isDiff_scale u (hX i) (s (c i)))
    have h3 : IsTangent v := by
      rw [(Chart.isLieComb_iff _ x v).1 h1]
      exact (Chart.isTan_iff _).1 h2.1
    exact (t1 v h3).unique hW (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u X x _ v hxt hX h1)
  rw [key c w v W hw hv hW, key c' w' v' W' hw' hv' hW', hermForm_sum_sum, form_eq_sum_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [d₀, hermForm_eq hU a₀ hQ b₀ hA F.basis.1 c₀ (fun i => ⟨hx i, hX i⟩)]
  ring

end GlobalTheory.CM.LieMetric
end
end

