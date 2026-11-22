import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCohSubDegEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv sabT sabM)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.FlagMod GlobalTheory.LocM GlobalTheory.NefCurveTest
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.NefStep

section Span

variable {X : Scheme.{0}} {F : X.Modules} {J : Type} {T : J → X.Opens} {r : ℕ}
  (w : ∀ j, Fin r → Γ(F, T j)) (l : ∀ j, Fin r → Γ(VB.dual F, T j))

def spanSub : Sub F where
  sec V :=
    { carrier := {s | ∀ j (W : X.Opens) (h₁ : W ≤ V) (h₂ : W ≤ T j),
        resM F h₁ s = ∑ a, dualApp (l j a) h₂ (resM F h₁ s) • resM F h₂ (w j a)}
      add_mem' := fun hs ht j W h₁ h₂ => by
        simp only [map_add, add_smul, Finset.sum_add_distrib]
        rw [← hs j W h₁ h₂, ← ht j W h₁ h₂]
      zero_mem' := fun j W h₁ h₂ => by simp
      smul_mem' := fun a s hs j W h₁ h₂ => by
        simp only [resM_smul, map_smul, smul_assoc, ← Finset.smul_sum]
        rw [← hs j W h₁ h₂] }
  res_mem h s hs j W h₁ h₂ := by rw [resM_resM]; exact hs j W _ h₂
  mem_of_local {V s} H j W h₁ h₂ := by
    choose U hU hx hs using fun x : W => H x (h₁ x.2)
    refine Twist.sec_ext_of_cover (fun x => W ⊓ U x) (fun _ => inf_le_left)
      (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx', hx _⟩) fun x => ?_
    have := hs x j (W ⊓ U x) inf_le_right (inf_le_left.trans h₂)
    simp only [map_sum, resM_smul, ← dualApp_resM, resM_resM] at this ⊢
    exact this

theorem exists_sub_det {L : LB X} (hL : L.IsLB) (w : ∀ j, Fin r → Γ(F, L.U j)) (l : ∀ j, Fin r → Γ(VB.dual F, L.U j))
    (hl : ∀ j a b, dualApp (l j a) le_rfl (w j b) = if a = b then 1 else 0)
    (B : ∀ j j', Matrix (Fin r) (Fin r) Γ(X, L.U j ⊓ L.U j'))
    (hB : ∀ j j' b, resM F inf_le_right (w j' b) = ∑ a, B j j' a b • resM F inf_le_left (w j a))
    (hg : ∀ j j', (L.g j j').val = (B j j').det) :
    ∃ (W : X.Modules) (i : W ⟶ F), Mono i ∧ IsVB W r ∧ LBIso L (det W r) := by
  have hl' (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) (a) :
      dualApp (l j a) h (∑ b, c b • resM F h (w j b)) = c a := by
    have e (b) : dualApp (l j a) h (resM F h (w j b)) = if a = b then 1 else 0 := by
      rw [dualApp_resM (l j a) le_rfl h, hl]; split_ifs <;> simp
    simp [e]
  let N := spanSub w l
  have hm (j) (b) : w j b ∈ N.sec (L.U j) := fun j' V h₁ h₂ => by
    have e := congrArg (resM F (le_inf h₂ h₁)) (hB j' j b)
    simp only [map_sum, resM_smul, resM_resM] at e
    rw [e]
    simp only [hl']
  have hi (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) :
      N.incl.app V (∑ b, c b • resM _ h (N.mkSec _ (hm j b))) = ∑ b, c b • resM F h (w j b) := by
    simp only [map_sum, Scheme.Modules.Hom.app_smul, app_resM, Sub.incl_app_mkSec]
  have he (j) : IsFrame fun b => N.mkSec _ (hm j b) := isFrame_iff.2 fun V h => by
    refine ⟨Fintype.linearIndependent_iff.2 fun c hc a => ?_, fun s _ =>
      (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun a => dualApp (l j a) h (resM F le_rfl (N.incl.app V s)),
        N.incl_app_injective V ((hi j h _).trans ?_)⟩⟩
    · rw [← hl' j h c a, ← hi, hc, map_zero, map_zero]
    · exact (N.incl_app_mem s j V le_rfl h).symm.trans (resM_self _ _)
  refine ⟨N.toMod, N.incl, inferInstance, lbIso_det_of_frames hL _ he fun j j' => Units.ext ?_⟩
  rw [hg, IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  have e : resM _ inf_le_right (N.mkSec _ (hm j' b)) =
      ∑ a, B j j' a b • (he j).basis (inf_le_left : L.U j ⊓ L.U j' ≤ _) a := by
    simp only [IsFrame.basis_apply]
    refine N.incl_app_injective _ (Eq.trans ?_ (hi j _ _).symm)
    rw [app_resM, Sub.incl_app_mkSec, hB]
  rw [Module.Basis.toMatrix_apply, e, Module.Basis.repr_sum_self]

end Span

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)

open Classical in

theorem LL_stepEx_g_inv (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) (k k' : F.J) :
    ((show Γ(Z, F.U k ⊓ F.U k')ˣ from (F.LL (stepEx σ n)).g k k')⁻¹).val =
      ∏ a : Fin n, F.B k k' σ (a.castLE hn) (a.castLE hn) := by
  have e : (∏ ix, F.T k k' ix ^ (-stepEx σ n ix))⁻¹ = ∏ a : Fin n, F.T k k' (some ⟨σ, a.castLE hn⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun a : Fin n => (some ⟨σ, a.castLE hn⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun a _ => ?_).symm
    · simpa using h
    · rcases ix with _ | ⟨σ', i⟩
      · simp [stepEx]
      · have : ¬ (σ' = σ ∧ (i : ℕ) < n) := by
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, by simp, rfl⟩
        simp [stepEx, this]
    · simp [stepEx]
  refine (congrArg Units.val e).trans ?_
  rw [Units.coe_prod]
  rfl

theorem left_vecAt {S S' : Type} [CommRing S] [CommRing S'] (k : F.J) (φ : S →+* S') {z : Sp S ⟶ Z} {z' : Sp S' ⟶ Z}
    (e : spMap φ ≫ z = z') (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z' hz' rfl σ a)).left = spMap (Formalism.L2.Pj.dualMap φ) ≫ (tv (F.vecAt k z hz rfl σ a)).left := by
  subst e
  rw [← F.tanPull_vecAt k φ z hz hz' rfl rfl (Category.assoc _ _ _).symm, tanPull_left]

theorem exists_step_sub {C : Scheme.{0}} [C.IsSeparated] [PreconnectedSpace C] (g : C ⟶ Z) {t : SAB H C}
    (m : SABMap t Y.t (g ≫ π)) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (i : W ⟶ Lie t.G), Mono i ∧ IsVB W n ∧
      LBIso (CechPic.dual ((F.LL (stepEx σ n)).pull g)) (det W n) := by
  have := t.semi
  obtain ⟨Ψ, hΨ⟩ := exists_tangent_equiv m
  obtain ⟨d, -, hd⟩ := exists_isVB_of_isSemiAbelian t.G
  have := hd.isQuasicoherent
  let J := {q : C.Opens × F.J // CoordOpen t q.1 ∧ q.1 ≤ g ⁻¹ᵁ F.U q.2}
  have hin {T : C.Opens} (hT : IsAffineOpen T) {U : Z.Opens} (h : T ≤ g ⁻¹ᵁ U) : ⊤ ≤ (affPt hT ≫ g) ⁻¹ᵁ U :=
    fun z hz => h (le_preimage_affPt hT hz)
  have hc : ⨆ j : J, j.1.1 = ⊤ := top_unique fun x _ => by
    obtain ⟨q, hq⟩ := Opens.mem_iSup.1 (F.cover.ge (Set.mem_univ (g x)))
    obtain ⟨T, hT, hx, hle⟩ := exists_coordOpen t (V := g ⁻¹ᵁ F.U q) hq
    exact Opens.mem_iSup.2 ⟨⟨(T, q), hT, hle⟩, hx⟩
  let M := CechPic.dual ((F.LL (stepEx σ n)).pull g)
  have hM : M.IsLB := isLB_dual (LB.isLB_pull (F.isLB_LL _) g)
  have hle (j : J) : j.1.1 ≤ M.U fun _ => j.1.2 := j.2.2.trans (GlobalTheory.LB.pull_U (L := F.LL _) g fun _ => j.1.2).ge
  have hL := TriangularFrames.isLB_refine hc hM (fun j : J => fun _ => j.1.2) hle
  let ψ (j : J) := Ψ _ j.2.1 ((affPt j.2.1.1 ≫ g) ≫ π) (Category.assoc _ _ _).symm
  let b (j : J) := (lieBasis (F.M j.1.2).toMChart _ (F.inM (hin j.2.1.1 j.2.2) rfl)).map (ψ j)
  have hb (j : J) : IsFrame (b j) := Summand.isFrame_of_affine_basis j.2.1.1 _
  choose p hp using fun j : J => F.uAt_split j.1.2 _ (hin j.2.1.1 j.2.2) σ
  have hT (j j' : J) : CoordOpen t (j.1.1 ⊓ j'.1.1) := j.2.1.mono (j.2.1.1.inf j'.2.1.1) inf_le_left
  have hh (j j' : J) := hin (hT j j').1 ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
  have hres (j : J) {T : C.Opens} (hT : CoordOpen t T) (h : T ≤ j.1.1) (a : Fin (Dw.mult σ)) :
      resM (Lie t.G) h (ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ a)) =
        Ψ T hT _ (Category.assoc _ _ _).symm (F.vecAt j.1.2 _ (hin hT.1 (h.trans j.2.2)) rfl σ a) := by
    exact (hΨ _ _ _ _ _ _ _ _ h _ _ (left_vecAt F _ _ (by rw [← Category.assoc, spMap_affPt]) _ _ _ _)).symm
  let w (j : J) (a : Fin n) : Γ(Lie t.G, j.1.1) := ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ (a.castLE hn))
  let f (j : J) (a : Fin n) : Γ(VB.dual (Lie t.G), j.1.1) := ∑ s, p j (a.castLE hn) s • (hb j).coord s
  let B (j j' : J) : Matrix (Fin n) (Fin n) Γ(C, j.1.1 ⊓ j'.1.1) :=
    ((F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j'))).submatrix (Fin.castLE hn) (Fin.castLE hn)
  have h₁ (j : J) (a a' : Fin n) : dualApp (f j a) le_rfl (w j a') = if a = a' then 1 else 0 := by
    have e := congrFun (congrFun (hp j) (a.castLE hn)) (a'.castLE hn)
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Fin.castLE_inj] at e
    rw [← e, dualApp_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e' : w j a' = ∑ s, F.uAt j.1.2 _ (hin j.2.1.1 j.2.2) σ s (a'.castLE hn) • (hb j).basis le_rfl s := by
      simp only [w, Frames.vecAt, vec_apply, map_sum, map_smul, IsFrame.basis_apply, resM_self, b,
        Module.Basis.map_apply]
    rw [dualApp_smul, LinearMap.smul_apply, IsFrame.dualApp_coord, e', Module.Basis.repr_sum_self, GlobalTheory.LB.resG_self,
      smul_eq_mul]
  have h₂ (j j' : J) (a : Fin n) : resM (Lie t.G) (inf_le_right : j.1.1 ⊓ j'.1.1 ≤ _) (w j' a) =
      ∑ s, B j j' s a • resM (Lie t.G) inf_le_left (w j s) := by
    refine (hres j' (hT j j') inf_le_right _).trans ?_
    rw [F.vecAt_eq_sum j.1.2 j'.1.2 _ (hin (hT j j').1 (inf_le_left.trans j.2.2)) _ (hh j j'), map_sum]
    refine (Finset.sum_of_injOn (Fin.castLE hn) (Fin.castLE_injective hn).injOn (fun _ _ => Finset.mem_univ _)
      (fun s _ h => ?_) fun s _ => ?_).symm
    · have hs : a.castLE hn < s := lt_of_not_ge fun h' => h ⟨⟨s, lt_of_le_of_lt h' a.2⟩, by simp, rfl⟩
      have h0 : (F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j')) s (a.castLE hn) = 0 := F.B_map_tri _ _ σ _ hs
      rw [h0, zero_smul, map_zero]
    · rw [map_smul, ← hres j (hT j j') inf_le_left]
      rfl
  have h₃ (j j' : J) : resG C (inf_le_inf (hle j) (hle j')) (M.g (fun _ => j.1.2) fun _ => j'.1.2).val =
      (B j j').det := by
    have ht : (B j j').BlockTriangular id := fun s s' h =>
      F.B_map_tri j.1.2 j'.1.2 σ (ev _ _ (hh j j')) (i := s.castLE hn) (j := s'.castLE hn) h
    rw [Matrix.det_of_upperTriangular ht]
    simp only [B, Matrix.submatrix_apply, Matrix.map_apply, ← map_prod]
    rw [← LL_stepEx_g_inv F σ hn]
    refine left_inv_eq_right_inv (a := ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val) ?_
      ((map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _)))
    have e : ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val = resG C (inf_le_inf (hle j) (hle j'))
        (((F.LL (stepEx σ n)).pull g).g (fun _ => j.1.2) fun _ => j'.1.2).val := by
      refine Eq.trans ?_ (GlobalTheory.LB.resG_pull_g (L := F.LL _) g _ _ _).symm
      refine (ev_appLE (affPt (hT j j').1) g ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
        (le_preimage_affPt _) _ _).symm.trans ?_
      exact congr($(ev_tau_self (hT j j').1 _) _)
    refine (congrArg (_ * ·) e).trans ((map_mul _ _ _).symm.trans ?_)
    exact (congrArg _ (Units.inv_mul _)).trans (map_one _)
  obtain ⟨W, i, hi, hW, e⟩ := exists_sub_det (F := Lie t.G) hL w f h₁ B h₂ h₃
  exact ⟨W, i, hi, hW, (cls_eq_iff hM hW.isLB_det).1 (((cls_eq_iff hL hM).2
    (TriangularFrames.lbIso_refine hM _ hle)).symm.trans ((cls_eq_iff hL hW.isLB_det).2 e))⟩

theorem curveTest_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] (σ : E →+* ℂ)
    {n : ℕ} (hn : n ≤ Dw.mult σ) : CurveTest K (F.LL (stepEx σ n)) := fun C _ hs hp hc g => by
  have := LieSemineg.isIntegral_curve hs hc
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : C.IsSeparated := ⟨by rw [← terminal.comp_from (strHom K C)]; infer_instance⟩
  obtain ⟨W, i, _, hW, e⟩ := exists_step_sub F g (sabM Out.proved_CubePullSt (g ≫ π) Y.t) σ hn
  have := (sabT Out.proved_CubePullSt (g ≫ π) Y.t).semi
  have hM := LB.isLB_pull (F.isLB_LL (stepEx σ n)) g
  refine (h.dual_det_nonneg hs hp hc _ hW i).trans_eq (interNum_congr_cls K _ (isLB_vecOne (isLB_dual hW.isLB_det))
    (isLB_vecOne hM) fun j => ?_)
  fin_cases j
  change cls _ (isLB_dual hW.isLB_det) = cls _ hM
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff (isLB_dual hM) hW.isLB_det).2 e, cls_dual hM, neg_neg]

theorem isNef_pull_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) (k : Type) [Field k]
    [CharZero k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] (g : X ⟶ Z) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    IsNef k ((F.LL (stepEx σ n)).pull g) :=
  ((curveTest_LL_stepEx F h (AlgebraicClosure k) σ hn).pull (F.isLB_LL _) g).isNef hN (LB.isLB_pull (F.isLB_LL _) g)

end GlobalTheory.NefStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegOfGenericFiniteNormalExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenExt

attribute [local instance] ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK

theorem grp : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E), ∃ (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ ∧ IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ ∧ κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧ κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  haveI : IsNoetherianRing R' := hR.1
  haveI : IsIntegrallyClosed R' := hR.2.2.1
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have g1 := (pull_grp q₁).congr sc rfl
  have g2 := (pull_grp q₂).congr sc rfl

  obtain ⟨κ, k₁, k₂⟩ : ∃ κ : E.P.A.left ⟶ D₃.P.A.left, κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧
      κ ≫ D₃.P.A.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gpp.1.lift _ _ (g1.1.w.trans (Category.assoc _ _ _).symm), gpp.1.lift_fst _ _ _, gpp.1.lift_snd _ _ _⟩
  have gκ : IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ :=
    IsGrpPullback.cancel gpp (g1.congr rfl k₁.symm) k₂

  let G₂ := (Over.pullback (specOf ρ)).obj D₂.P.A
  have gb : IsGrpPullback G₂ D₂.P.A (spMap ρ) (pullback.fst D₂.P.A.hom (specOf ρ)) := isGrpPullback_pullback _ _
  obtain ⟨κ₂, l₁, l₂⟩ : ∃ κ₂ : E.P.A.left ⟶ G₂.left, κ₂ ≫ pullback.fst D₂.P.A.hom (specOf ρ) = GlobalTheory.PsiEvenPull.proj q₂ ∧
      κ₂ ≫ G₂.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gb.1.lift _ _ (g2.1.w.trans (Category.assoc _ _ _).symm), gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gκ₂ : IsGrpPullback E.P.A G₂ (spMap (algebraMap R' (FractionRing R'))) κ₂ :=
    IsGrpPullback.cancel gb (g2.congr rfl l₁.symm) l₂
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R') (jK R') := .fractionField R' (FractionRing R')
  have s₃ : IsSemiAbelian D₃.P.A := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D₃.P.isAb
  have s₂ : IsSemiAbelian G₂ :=
    GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ D₂.P.isAb)
  obtain ⟨F, ⟨hF, hκ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj s₃ s₂ gκ gκ₂
  refine ⟨F.hom.left ≫ pullback.fst D₂.P.A.hom (specOf ρ), κ, ?_, gκ, k₁, ?_⟩
  · exact ((isGrpPullback_of_iso F).comp gb).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, hκ, l₁]

theorem bundle : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.polarisationBundleIso_generic_extends_normalLocal R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w, hw, hr⟩ := GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification R R' ρ D₂ D₃ Φ gp w₀ hw₀
  exact ⟨w, hw, hr, GlobalTheory.T.rigidified_identifications_generic_fibre_agree R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ w hw hr⟩

theorem cpt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ x : D₃.X, (D₃.c x).left ≫ Φ = spMap ρ ≫ (D₂.c (q₂.xe (q₁.xe.symm (p.xe x)))).left := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ x
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = jK R' ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have hx : (E.c y).left ≫ κ = jK R' ≫ (D₃.c x).left := by
    apply gpp.1.hom_ext
    · show ((E.c y).left ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
      rw [Category.assoc, h₁, cq, Category.assoc, cp, sc, Category.assoc]
    · rw [Category.assoc, gκ.1.w, ← Category.assoc, b1, Category.id_comp, Category.assoc, b3]
      exact (Category.comp_id _).symm
  have c2 : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₂ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₂.c (q₂.xe y)).left := q₂.c_pr y
  have hsep := (GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian D₂.P.A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme D₂.P.A D₂.P.isAb)).2
  have b2 : (D₂.c (q₂.xe y)).left ≫ D₂.P.A.hom = 𝟙 _ := by simpa using Over.w (D₂.c (q₂.xe y))
  haveI := hsep
  refine ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R')) D₂.P.A.hom ?_ (jK R') ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, b3, Category.assoc, b2]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rw [← Category.assoc, ← hx, Category.assoc, h₂, c2, sc, Category.assoc]

end GlobalTheory.Mum.GenExt

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem isPullDeg_of_generic : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')), IsPullDeg ρ D₁ D₃ → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E → Nonempty (IsPullDeg ρ D₂ D₃) := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  have hα : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' _
  obtain ⟨Φ, κ, gp, gκ, h₁, h₂⟩ := GenExt.grp R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  obtain ⟨w, hw, hr, hT⟩ := GenExt.bundle R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  have hc := GenExt.cpt R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift (show Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) from hα.comp hρ) q₂

  let lf : FractionRing (FractionRing R') →+* FractionRing R' :=
    IsFractionRing.lift (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id
  let r' : (TK R').left ⟶ (TK (FractionRing R')).left := spMap lf
  have hrj : r' ≫ jK (FractionRing R') = 𝟙 _ := by
    show spMap lf ≫ spMap (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = 𝟙 _
    rw [← spMap_comp]
    have : lf.comp (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = RingHom.id _ :=
      RingHom.ext fun a => IsFractionRing.lift_algebraMap (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id a
    rw [this]; exact Spec.map_id _
  have hr2 : r' ≫ jK (FractionRing R') ≫ spMap ((algebraMap R' (FractionRing R')).comp ρ) =
      GlobalTheory.ArcPull.genMap hρ ≫ jK R := by
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hrj, Category.id_comp]
    exact (spMap_comp ρ (algebraMap R' (FractionRing R'))).trans ((Category.id_comp _).symm.trans (GlobalTheory.ArcPull.fracMap_sq hρ))
  refine ⟨(GlobalTheory.DvrDeg.exists_isPullDeg_of_val hρ D₂ D₃ q₂.psiW s hs gp w hw hr
    (p.xe.trans (q₁.xe.symm.trans q₂.xe)) hc (fun x z J J' hJ hJ' => ?_)).choose⟩
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  set e : (TK R').left ⟶ E.P.A.left := r' ≫ E.xK y with he
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have a1 : (e ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by
    rw [Category.assoc, h₁]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
    rw [Category.assoc, Category.assoc, cq, Category.assoc, cp, ← Category.assoc (jK (FractionRing R')),
      ← Category.assoc r', hr2, ← Category.assoc (jK R'), ← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  have a2 : (e ≫ κ) ≫ D₃.P.A.hom = D₃.xK x ≫ D₃.P.A.hom := by
    rw [Category.assoc, gκ.1.w]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) =
      (jK R' ≫ (D₃.c x).left) ≫ D₃.P.A.hom
    simp only [Category.assoc, reassoc_of% b1, b3, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, hrj, Category.id_comp]; rfl
  have hx : e ≫ κ = D₃.xK x := gpp.1.hom_ext a1 a2
  obtain ⟨JE, hJE⟩ := GlobalTheory.DegPull.exists_good' E.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.DegPull.exists_good' D₁.P.isLB z
  have v₂ := GlobalTheory.ArcPull.psi_val q₂ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ hJE y
  have v₁ := GlobalTheory.ArcPull.psi_val q₁ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ₁ hJE y
  have v₃ := GlobalTheory.ArcPull.psi_val p (GlobalTheory.ArcPull.genMap hρ) (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' x
  rw [hy'] at v₁
  rw [v₁, Category.id_comp] at v₃
  have ex₂ : e ≫ GlobalTheory.PsiEvenPull.proj q₂ = D₃.xK x ≫ Φ := by rw [← h₂, ← Category.assoc, hx]
  have ex₁ : e ≫ GlobalTheory.PsiEvenPull.proj q₁ = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by rw [← h₁, ← Category.assoc, hx]
  have t := hT _ e z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) (JE e) (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p))
    (by rw [← Scheme.Hom.comp_apply, ex₂]; exact hJ _) (by rw [← Scheme.Hom.comp_apply, hx]; exact hJ' _) (hJE e)
    (by rw [← Scheme.Hom.comp_apply, ex₁]; exact hJ₁ _)
  simp only [hx] at t
  have o₂ : GlobalTheory.ArcPull.om q₂.w z J JE e = gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₂]
  have o₁ : GlobalTheory.ArcPull.om q₁.w z J₁ JE e = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₁]
  have oo : GlobalTheory.ArcPull.om w z J J' (D₃.xK x) = gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) := rfl
  have op : GlobalTheory.ArcPull.om p.w z J₁ J' (D₃.xK x) =
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := rfl
  change val (D₂.psi (q₂.xe y)) _ z J = _
  rw [v₂, oo, o₂]
  rw [o₁, op] at v₃
  have v₄ : val (E.psi y) r' z JE = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) *
      ((gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)))⁻¹ *
        val (D₃.psi x) (𝟙 _) z J') := by
    rw [← v₃, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  rw [v₄]
  have t' : gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) =
      gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) * (gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e))⁻¹ *
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := by
    rw [← t, inv_mul_cancel_right]
  rw [t']
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingFormalFibreMvPolynomialPerfectStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularRing_formal_fibre_mvPolynomial_perfect : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K] [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K], (∀ a : Λ, algebraMap (Localization.AtPrime P) K (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) → IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  first | exact @GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial | exact GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial | (intros; apply GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  first | exact @GlobalTheory.Mum.Conj.txFrame_frTw | exact GlobalTheory.Mum.Conj.txFrame_frTw | (intros; apply GlobalTheory.Mum.Conj.txFrame_frTw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomOfChart
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.BcPull

theorem isom_of_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (L M : MLine p σ)
    (e : M.B.ι → L.B.ι) (hU : ∀ a, M.B.U a ≤ L.B.U (e a))
    (hg : ∀ (x : X) a a', x ∈ M.B.U a → x ∈ M.B.U a' →
      gm (𝟙 X) x (M.B.U a ⊓ M.B.U a') (M.B.g a a') = gm (𝟙 X) x (L.B.U (e a) ⊓ L.B.U (e a')) (L.B.g (e a) (e a')))
    (hφ : ∀ a, ∀ y ∈ ptsIn p σ (M.B.U a), M.φ.φ a y = L.φ.φ (e a) y) : L.Isom M := by
  have le (c : M.B.ι × L.B.ι) : M.B.U c.1 ⊓ L.B.U c.2 ≤ L.B.U (e c.1) ⊓ L.B.U c.2 := inf_le_inf_right _ (hU c.1)
  refine ⟨⟨fun c => res (le c) (L.B.g (e c.1) c.2)⟩, fun c c' => Geo.Tor.unit_ext fun x hx => ?_, fun a b y ha hb => ?_⟩
  · have hx' : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ (M.B.U c'.1 ⊓ L.B.U c'.2) := hx
    refine ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c) hx'.1 _)).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (Geo.Tor.gm_div L.B M.B (𝟙 X) x c c' hx')
      ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c') hx'.2 _))).trans ?_)
    have h₁ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) (hU _ hx'.2.1) hx'.2.2
    have h₂ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) hx'.1.2 hx'.2.2
    rw [hg x _ _ hx'.1.1 hx'.2.1, mul_right_comm, h₁, ← h₂, mul_inv_cancel_right]
  · rw [hφ a y ha, L.φ.trans (e a) b y (ptsIn_mono (hU a) ha) hb, sub_add_eq_add_sub, eq_sub_iff_add_eq]
    exact congrArg (fun z : ℂ => _ + Real.log (‖z‖ ^ 2))
      (CxPts.ev_res (le (a, b)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) _).symm

theorem bc_φ {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    {ρ : k →+* K} (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) (i : PUnit → A.B.ι) (z : CxPts q τ) :
    (A.bc w τ).φ.φ i z = A.φ.φ (i PUnit.unit) (bcPt w τ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * A.φ.φ (i a) (bcPt w τ z)).trans (by simp)

theorem bc_pull_isom : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G Z G' : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (w : j ≫ p = q ≫ spMap ρ) (i : Z ⟶ X) (j' : G' ⟶ Z) (g : G' ⟶ G), g ≫ j = j' ≫ i → ∀ (w' : j' ≫ i ≫ p = (g ≫ q) ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)), ((A.pull i rfl).bc w' τ).Isom ((A.bc w τ).pull g rfl) := by
  intro k K _ _ ρ X G Z G' p q j w i j' g h w' τ A
  have hm (a : PUnit → PUnit → A.B.ι) (x : G') (hx : x ∈ ((A.B.pull j).pull g).U a) :
      x ∈ ((A.B.pull i).pull j').U a := by
    have h₀ : j (g x) ∈ A.B.U (a PUnit.unit PUnit.unit) := Geo.Tor.mem_pull.1 (Geo.Tor.mem_pull.1 hx)
    have h₁ : (g ≫ j) x ∈ A.B.U (a PUnit.unit PUnit.unit) := h₀
    rw [h] at h₁
    exact Geo.Tor.mem_pull.2 (Geo.Tor.mem_pull.2 h₁)
  refine isom_of_chart _ _ (fun a : PUnit → PUnit → A.B.ι => a) hm
    (fun x (a a' : PUnit → PUnit → A.B.ι) ha ha' => ?_) fun (a : PUnit → PUnit → A.B.ι) y _ => ?_
  · refine ((Geo.Tor.gm_pull_g (A.B.pull j) g (𝟙 G') x a a' ha ha').trans
      (Geo.Tor.gm_pull_g A.B j (𝟙 G' ≫ g) x _ _ (Geo.Tor.mem_pull.1 ha) (Geo.Tor.mem_pull.1 ha'))).trans (Eq.symm ?_)
    refine ((Geo.Tor.gm_pull_g (A.B.pull i) j' (𝟙 G') x a a' (hm a x ha) (hm a' x ha')).trans
      (Geo.Tor.gm_pull_g A.B i (𝟙 G' ≫ j') x _ _ (Geo.Tor.mem_pull.1 (hm a x ha))
        (Geo.Tor.mem_pull.1 (hm a' x ha')))).trans ?_
    rw [Category.assoc, Category.assoc, h]
  · refine (((A.bc w τ).φ.pull_φ g rfl a y).trans (bc_φ w τ A _ _)).trans (Eq.symm ?_)
    refine ((bc_φ w' τ (A.pull i rfl) a y).trans (A.φ.pull_φ i rfl _ _)).trans (congrArg _ (Subtype.ext ?_))
    change (y.1 ≫ j') ≫ i = (y.1 ≫ g) ≫ j
    rw [Category.assoc, Category.assoc, h]

end GlobalTheory.Mix.BcPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeEqHilbertEisensteinJetStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_derivative_eq_hilbert_eisenstein_jet : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t : ℂ) (κ : Emb F → ℕ) (u : List (Emb F)), 0 < τ.im → (∀ i, u.count i = κ i) → iterD u (fun z ↦ (cK F (2 * s) : ℂ) * gval (2 * s) L (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 = jet (2 * s) L κ τ c t := by
  first | exact @GlobalTheory.HilbFam.iterD_eq_jet_of_count | exact GlobalTheory.HilbFam.iterD_eq_jet_of_count | (intros; apply GlobalTheory.HilbFam.iterD_eq_jet_of_count <;> assumption)
end

