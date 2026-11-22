import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsReg
open GlobalTheory.Points

theorem valR_appIso_inv {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (U : X.Opens) (f : Γ(X, U))
    {C : Type} [CommRing C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    valR (y ≫ j) (j ''ᵁ U) ((j.appIso U).inv.hom f) = valR y U f := by
  rw [← valR_appLE y j (j.preimage_image_eq U).ge hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res y le_rfl hy f

theorem valR_valueAt {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ) [GrpObj A] {T : Over B}
    {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [CommRing K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) = valR x ⊤ v * valR x _ (τ.s fun _ => j).val := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  exact e

theorem range_subset {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) {U : X.Opens} (p : Sp K) (h : x p ∈ U) :
    Set.range x ⊆ U := by
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y p]
  exact h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_eq_mul_unit (hne : (U₀ : Set M.Z).Nonempty) {N : M.Z.Opens} {σ : Q.SecFam N} {c : Ω}
    (hσ : Q.ThMul c N σ) {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.left} {w : W.toScheme}
    (hE : Q.ExtPt a W h) (hF : Q.FrameUnit a W h w) (hw : W.ι w ∈ N) (jL : Q.L.L.ι) (hj : h w ∈ Q.L.L.U jL) :
    ∃ (T : M.Z.Opens) (f : Γ(M.Z, T)) (e : Ω), W.ι w ∈ T ∧ e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w) ∧
      c * S.th a = valF M.pt T f * e⁻¹ ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), Set.range y = {w} →
        valF (y ≫ W.ι) T f = valF (y ≫ h) _ (σ fun _ => jL) := by
  let V : W.toScheme.Opens := h ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL)
  have hwV : w ∈ V := by
    refine ⟨?_, Set.mem_iInter.2 fun _ => hj⟩
    change (h ≫ Q.G.hom) w ∈ N
    rw [hE.1]
    exact hw
  have hT : W.ι w ∈ W.ι ''ᵁ V := ⟨w, hwV, rfl⟩
  have hval : ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), ⊤ ≤ y ⁻¹ᵁ V →
      valF (y ≫ W.ι) (W.ι ''ᵁ V) ((W.ι.appIso V).inv.hom ((h.app _).hom (σ fun _ => jL))) =
        valF (y ≫ h) _ (σ fun _ => jL) := fun K _ y hy =>
    (valR_appIso_inv W.ι V _ y hy).trans (valR_comp y h _ _).symm
  have lift : ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι M.pt (by
      rw [Scheme.Opens.range_ι]
      exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hU)), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨x, hx⟩ := lift W ⟨w.1, w.2⟩
  obtain ⟨x₀, hx₀⟩ := lift U₀ hne
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  have hcond : (t₀ ≫ (ρ.pt a).left) ≫ ρ.P.A.hom = x₀ ≫ Q.u₀ := by
    rw [Q.u₀_gen x₀ hx₀, Category.assoc, Over.w (ρ.pt a)]
    exact Category.comp_id _
  let x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀ := pullback.lift _ _ hcond
  have h1 : x' ≫ pullback.fst _ _ = t₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have h2 : x' ≫ pullback.snd _ _ ≫ U₀.ι = M.pt := by
    rw [← Category.assoc, pullback.lift_snd, hx₀]
  have h3 : x' ≫ Q.φ ≫ Q.G.hom = M.pt := by
    rw [← h2]
    exact congrArg (x' ≫ ·) Q.cart.1.w
  have h4 : x ≫ h = x' ≫ Q.φ := hE.2 x x' hx h3 h1
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := by
    have h5 := M.top_le_preimage_pt ⟨_, hT⟩
    rw [← hx] at h5
    exact le_preimage_mono x (W.ι.preimage_image_eq V).le h5
  have hxh : Set.range (x' ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL : Q.G.left.Opens) := by
    rw [← h4]
    exact (top_le_preimage_iff _ _).1 hxV
  obtain ⟨jP, hjP⟩ : ∃ jP, Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U jP := by
    have h5 : (t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω) ∈ ⨆ i, ρ.P.L.U i := by
      rw [ρ.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    exact ⟨i, range_subset _ _ hi⟩
  obtain ⟨he0, he1, he2⟩ := hF jP jL x' _ hj h3 h1 (h1 ▸ hjP) rfl
  refine ⟨_, _, _, hT, he0, he1, he2, ?_, fun K _ y hy => hval K y fun p _ => ?_⟩
  · have hr : (t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        x' ≫ pullback.fst _ _ := by
      rw [h1, Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
    have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := Spec.map_id _
    have e := hσ Ω (RingHom.id Ω) x' _ jP jL (by rw [h2, hid, Category.id_comp]) hr (h1 ▸ hjP)
      (fun p hp => Set.mem_iInter.1 (hxh hp).2 0) (fun p hp => (hxh hp).1)
    have e2 := valR_valueAt ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ jP hjP
    have e3 : valR (X := (baseOver (Sp S.R)).left) t₀ ⊤ (fn (⟨S.th a, S.th_mem a⟩ : S.R)) = S.th a :=
      valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _
    rw [e3] at e2
    rw [Fintype.sum_unique, zpow_one, RingHom.id_apply, valF_eq_valR, e2, ← h4, ← hval Ω x hxV, hx] at e
    have hn := (div_ne_zero_iff.1 he0).1
    rw [inv_div, ← mul_div_assoc, eq_div_iff hn, _root_.mul_assoc, _root_.mul_comm (valF M.pt _ _)]
    exact e
  · have h5 : y p ∈ Set.range y := ⟨p, rfl⟩
    rw [hy] at h5
    change y p ∈ V
    rw [show y p = w from h5]
    exact hwV

end GlobalTheory.ZH.TorsReg

open GlobalTheory.Points GlobalTheory.ZH.TorsReg in

theorem GlobalTheory.ZH.mul_theta_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N σ c _ hσ a W h w hE hF hw
  constructor
  · have h5 : h w ∈ ⨆ i, Q.L.L.U i := by
      rw [Q.L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    obtain ⟨T, f, e, hT, -, -, he, hc, -⟩ := exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [hc]
    exact mul_mem (RatModel.valF_mem_O hT f) he
  · intro K _ x j hx hv
    have hxw : x (IsLocalRing.closedPoint K) = w := by
      have h5 : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at h5
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
    have hi : h w ∈ Q.L.L.U i := by
      by_contra hi
      refine hv (dif_neg fun hle => hi ?_)
      rw [← hxw]
      exact Set.mem_iInter.1 (hle (x := IsLocalRing.closedPoint K) trivial).2 0
    obtain ⟨T, f, e, hT, he0, he1, -, hc, hK⟩ := exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [← hK K x hx] at hv
    have hxw' : (x ≫ W.ι) (IsLocalRing.closedPoint K) = W.ι w := by rw [← hxw]; rfl
    have hle : ⊤ ≤ (x ≫ W.ι) ⁻¹ᵁ T := (le_preimage_iff _ _).2 (hxw' ▸ hT)
    have hb : W.ι w ∈ M.Z.basicOpen f :=
      hxw' ▸ (le_preimage_iff _ _).1 ((le_preimage_basicOpen_iff _ hle f).2 (isUnit_iff_ne_zero.2 hv))
    obtain ⟨hf0, hf1⟩ := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hT f).2 hb)
    rw [hc]
    refine ⟨mul_ne_zero hf0 (inv_ne_zero he0), ?_⟩
    rw [_root_.mul_inv, inv_inv]
    exact mul_mem hf1 he1

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionRestrictionUnitTwist
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_trans_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem scale_mem_secOn {X : Scheme.{0}} (L : LB X) {V V' : X.Opens} (h : V' ≤ V) (a : Γ(X, V'))
    {σ : ∀ j, Γ(X, V ⊓ L.U j)} (hσ : σ ∈ secOn L V) :
    (fun j => resG X inf_le_left a * resG X (inf_le_inf_right _ h) (σ j)) ∈ secOn L V' := by
  intro i j
  have e := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    V' ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hσ i j)
  simp only [map_mul, resG_trans_apply] at e ⊢
  rw [e, mul_left_comm]

theorem valF_scale {X Z : Scheme.{0}} (p : X ⟶ Z) {N N' : Z.Opens} (h : p ⁻¹ᵁ N' ≤ p ⁻¹ᵁ N) (F : Γ(Z, N'))
    (U : X.Opens) (s : Γ(X, p ⁻¹ᵁ N ⊓ U)) {K : Type} [Field K] (g : Sp K ⟶ X)
    (hg : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ N' ⊓ U)) :
    valF g (p ⁻¹ᵁ N' ⊓ U) (resG X inf_le_left ((p.app N').hom F) * resG X (inf_le_inf_right _ h) s) =
      valF (g ≫ p) N' F * valF g _ s := by
  rw [valF_eq_valR, valR_mul g _ hg, valR_res g _ hg, valR_res g _ hg, ← valR_comp]
  rfl

theorem RatModel.exists_unit_fn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (N' : M.Z.Opens) (f : Ω) (hf : ∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) :
    ∃ F : Γ(M.Z, N'), (∀ z ∈ N', z ∈ M.Z.basicOpen F) ∧ ((N' : Set M.Z).Nonempty → valF M.pt N' F = f) := by
  by_cases hN : (N' : Set M.Z).Nonempty
  · obtain ⟨F, hF⟩ := (RatModel.mem_ringOn_iff_exists hN).1 (RatModel.mem_ringOn.2 fun z hz => (hf z hz).2.1)
    subst hF
    exact ⟨F, fun z hz => (RatModel.isUnit_valF_iff hz F).1
      ((RatModel.isUnit_O_iff _).2 ⟨(hf z hz).1, (hf z hz).2.2⟩), fun _ => rfl⟩
  · exact ⟨1, fun z hz => (hN ⟨z, hz⟩).elim, fun h => (hN h).elim⟩

theorem ZHPre.exists_scale_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N N' σ c f hN hf hσ hT hF
  obtain ⟨F, hFu, hFv⟩ := M.exists_unit_fn N' f hf
  have h : Q.G.hom ⁻¹ᵁ N' ≤ Q.G.hom ⁻¹ᵁ N := fun _ hz => hN hz
  refine ⟨_, scale_mem_secOn Q.LOne h ((Q.G.hom.app N').hom F) hσ, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    have e := hT K β g r jP jL h1 h2 h3 h4 (h5.trans h)
    have hg : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U (fun _ => jL)) := fun w _ =>
      ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
    have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
      rw [Category.assoc, Q.cart.1.w, ← h1]
      rfl
    have hne : (N' : Set M.Z).Nonempty := ⟨_, h5 ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have hv := valF_scale Q.G.hom h F _ (σ fun _ => jL) _ hg
    rw [hp, valF_eq_valR (spMap β ≫ M.pt), valR_spMap_comp β M.pt N' (M.top_le_preimage_pt hne),
      ← valF_eq_valR, hFv hne] at hv
    refine Eq.trans ?_ (congrArg (_ * ·) hv.symm)
    refine Eq.trans ?_ ((congrArg (β f * ·) e).trans (mul_left_comm _ _ _))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [map_mul, _root_.mul_assoc]
  · intro K _ _ x hx
    obtain ⟨g, j, hg, hne⟩ := hF K x (hx.trans hN)
    have h1 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) := by
      by_contra hc
      exact hne (dif_neg hc)
    have hx' : ⊤ ≤ x ⁻¹ᵁ N' := (top_le_preimage_iff x N').2 hx
    have h2 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j) := fun w hw =>
      ⟨(show ⊤ ≤ (g ≫ Q.G.hom) ⁻¹ᵁ N' from hg ▸ hx') hw, (h1 hw).2⟩
    refine ⟨g, j, hg, ?_⟩
    rw [valF_scale Q.G.hom h F _ (σ j) g h2, hg]
    exact mul_ne_zero ((le_preimage_basicOpen_iff x hx' F).1 fun w hw => hFu _ (hx' hw)).ne_zero hne

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionSectionEqIntegralPointAtTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem extPt_comp_eq_integral_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), Q.ExtPt a W h → ∀ (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) → ∀ yW : Sp u.V ⟶ W.toScheme, yW ≫ W.ι = yV → yW ≫ h = hV ≫ F := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT F ψ hM a W h hE hV x hx yW hyW
  obtain ⟨-, -, hK, hK0⟩ := hT
  obtain ⟨hF, hψ1, hψ2, hψ3⟩ := hM
  obtain ⟨hh, hE⟩ := hE
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hsep : IsSeparated Q.G.hom := Q.semi.separated
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hφ : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hFw : F ≫ Q.G.hom = u.G.hom ≫ yV := hF.1.w
  let sec : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hs1 : sec ≫ pullback.fst _ _ = Q.u₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have hs2 : sec ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hs3 : sec ≫ Q.φ ≫ Q.G.hom = U₀.ι := by
    rw [hφ, ← Category.assoc, hs2, Category.id_comp]
  let N : M.Z.Opens := W ⊓ U₀
  let iW : N.toScheme ⟶ W.toScheme := M.Z.homOfLE inf_le_left
  let iU : N.toScheme ⟶ U₀.toScheme := M.Z.homOfLE inf_le_right
  have hiW : iW ≫ W.ι = N.ι := M.Z.homOfLE_ι _
  have hiU : iU ≫ U₀.ι = N.ι := M.Z.homOfLE_ι _
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← hyW]
      exact (yW (jK u.V w)).2
    · rw [← hK]
      exact (yK w).2
  let k : Sp (FractionRing u.V) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (jK u.V ≫ yV) hr
  have hk : k ≫ N.ι = jK u.V ≫ yV := IsOpenImmersion.lift_fac _ _ _
  have hkW : k ≫ iW = jK u.V ≫ yW := by
    rw [← cancel_mono W.ι, Category.assoc, hiW, hk, Category.assoc, hyW]
  have hkU : k ≫ iU = yK := by
    rw [← cancel_mono U₀.ι, Category.assoc, hiU, hk, hK]
  have hne : (N : Set M.Z).Nonempty :=
    ⟨_, (k (IsLocalRing.closedPoint (FractionRing u.V))).2⟩
  have hg : Set.range M.pt ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let g : Sp Ω ⟶ N.toScheme := IsOpenImmersion.lift N.ι M.pt hg
  have hgN : g ≫ N.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (g ≫ N.ι) := by rw [hgN]; infer_instance
  have : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g N.ι
  have key : iW ≫ h = iU ≫ sec ≫ Q.φ := by
    refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ g ?_
    · simp only [Category.assoc]
      rw [hh, hs3, hiW, hiU]
    · have h1 : (g ≫ iU) ≫ U₀.ι = M.pt := by rw [Category.assoc, hiU, hgN]
      have := hE (g ≫ iW) (g ≫ iU ≫ sec) (by rw [Category.assoc, hiW, hgN])
        (by simp only [Category.assoc]; rw [hs3, hiU, hgN])
        (by
          simp only [Category.assoc]
          rw [hs1, ← Q.u₀_gen _ h1]
          simp only [Category.assoc])
      simpa only [Category.assoc] using this
  have hxψ : yK ≫ sec = x ≫ ψ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hs1, Category.assoc, hψ1, ← Category.assoc, hK0]
      exact hx4.symm
    · rw [Category.assoc, hs2, Category.assoc, hψ2, ← Category.assoc, hx3, Category.comp_id, Category.id_comp]
  have : IsDominant (jK u.V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap u.V (FractionRing u.V))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective u.V (FractionRing u.V))]
      exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ (jK u.V) ?_
  · simp only [Category.assoc]
    rw [hh, hyW, hFw, ← Category.assoc, hx1, Category.id_comp]
  · rw [← Category.assoc, ← hkW, Category.assoc, key, ← Category.assoc, hkU, ← Category.assoc, hxψ,
      Category.assoc, hψ3, ← Category.assoc, hx2, Category.assoc]

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermuteStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.torsionValues_coords_operator_permute : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), (∀ (K : Type) [Field K] (y : S.R →+* K) (a : S.Gam), ρ.Crd (spMap y ≫ (ρ.pt a).left) (fun i => y ⟨S.ev a i, S.ev_mem a i⟩)) ∧ ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n = algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i := by
  first | exact @GlobalTheory.ZH.EvCrd.ev_crd_act | exact GlobalTheory.ZH.EvCrd.ev_crd_act | (intros; apply GlobalTheory.ZH.EvCrd.ev_crd_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_cut_by_invariantRatios_field : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H) (a) (j : Fin d → C.I), GeometricallyConnected H.hom → C.Torus c i → C.Based c a j → C.KerIs a j i := by
  first | exact @GlobalTheory.ZJ.Charts.kerIs_of_torus | exact GlobalTheory.ZJ.Charts.kerIs_of_torus | (intros; apply GlobalTheory.ZJ.Charts.kerIs_of_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPower_sectionBasis_baseChange : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  first | exact @GlobalTheory.ZH.BasisBaseChange.basis_pullback | exact GlobalTheory.ZH.BasisBaseChange.basis_pullback | (intros; apply GlobalTheory.ZH.BasisBaseChange.basis_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelEqPullbackGroupScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem exists_iso_of_existsUnique_ext {B B' : Scheme.{0}} (j : B' ⟶ B) (G G' : Over B) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hext : ∀ (G G' : Over B) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f)
    (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj G') (he : IsMonHom e.hom) :
    ∃ E : G ≅ G', IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hext G G' hG hG' e.hom he
  obtain ⟨b, ⟨hb, hb'⟩, -⟩ := hext G' G hG' hG e.inv inferInstance
  refine ⟨⟨a, b, ?_, ?_⟩, ha, ha'⟩
  · exact (hext G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (hext G' G' hG' hG' (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ZHPre.exists_testMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∃ F ψ, Q.TestMap u yV yK F ψ := by
  intro hext o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT
  obtain ⟨-, -, h₁, h₂⟩ := hT
  have := u.U.gen_hom
  have gp₁ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  have gp₂ := ((isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK).comp
    (isGrpPullback_pullback ρ.P.A Q.u₀)).congr h₂ rfl
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso gp₁ gp₂
  have gp₃ := ((((isGrpPullback_of_iso e₁).comp
    (isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK)).congr (Category.id_comp _) rfl).comp Q.cart).congr h₁ rfl
  have gp₄ := (isGrpPullback_pullback ((Over.pullback yV).obj Q.G) (jK u.V)).comp (isGrpPullback_pullback Q.G yV)
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso gp₃ gp₄
  obtain ⟨E, mE, hE⟩ := exists_iso_of_existsUnique_ext (jK u.V) u.G ((Over.pullback yV).obj Q.G) u.semi
    (IsSemiAbelian.pullback _ Q.G Q.semi) (fun G G' _ _ => hext u.V (FractionRing u.V) G G') e₂ m₂
  refine ⟨E.hom.left ≫ pullback.fst Q.G.hom yV,
    e₁.hom.left ≫ pullback.fst ((Over.pullback Q.u₀).obj ρ.P.A).hom yK,
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback Q.G yV)).congr (Category.id_comp _) rfl, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans he₁
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (e₁.hom.left ≫ ·) (pullback.condition (f := ((Over.pullback Q.u₀).obj ρ.P.A).hom) (g := yK))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ yK) (Over.w e₁.hom))
  · refine he₂.symm.trans ?_
    have a : ((Over.pullback (jK u.V)).map E.hom).left ≫ pullback.fst ((Over.pullback yV).obj Q.G).hom (jK u.V) =
        pullback.fst u.G.hom (jK u.V) ≫ E.hom.left := pullback.lift_fst _ _ _
    rw [← hE]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst Q.G.hom yV) a).trans (Category.assoc _ _ _))

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationEqPolarFormOfWeightZeroMaxStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ) (g N : ℕ) (J : Type) (cls : J → X) (p : ℕ) [Fact p.Prime] (w : J → PadicAlgCl p) (ν : X →+ ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → Module.finrank ℤ X ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → (∀ i, Short q N (cls i)) → Ser q N cls w ν → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ m, ∀ α, ν α = QuadraticMap.polar q m α := by
  first | exact @GlobalTheory.ZH.ValLat.main | exact GlobalTheory.ZH.ValLat.main | (intros; apply GlobalTheory.ZH.ValLat.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuations_torusExtension_points : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J) ∧ (∀ g : GtPtF u.D.toPre (PadicAlgCl p), ∃ ν : u.D.toPre.X →+ ℝ, u.GtN g ν) ∧ (∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', u.GtN g ν → u.GtN g ν' → ν = ν') ∧ (∀ (g g' g'' : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', GtPtF.IsAdd g g' g'' → u.GtN g ν → u.GtN g' ν' → u.GtN g'' (ν + ν')) ∧ ∀ (y : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)), GtPtF.IsIota y g → u.GtN g (QuadraticMap.polar l.q y) := by
  first | exact @GlobalTheory.ZH.TorusVal.main | exact GlobalTheory.ZH.TorusVal.main | (intros; apply GlobalTheory.ZH.TorusVal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTestStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_labelledTorsion_uniformTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  first | exact @GlobalTheory.ZH.weilIs_uTest | exact GlobalTheory.ZH.weilIs_uTest | (intros; apply GlobalTheory.ZH.weilIs_uTest <;> assumption)
end

