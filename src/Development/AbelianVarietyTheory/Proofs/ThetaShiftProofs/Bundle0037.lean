import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAbelianTripleIsoOfSamePointValues
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FamilyIso

open GlobalTheory.MatchCoord GlobalTheory.AmpleSpan

section General

variable {F : Type} [Field F] {X Y Y' : Scheme.{0}} {L : LB X}

def pullP {p : Y ⟶ X} {p' : Y' ⟶ X} (h : Y' ⟶ Y) (e : p' = h ≫ p) {m : ℕ} (σ : SecP L p m) : SecP L p' m :=
  chartSec (chartPullSame L _ _ _ h fun _ => e) σ

theorem hasVal_pullP {p : Y ⟶ X} {p' : Y' ⟶ X} (h : Y' ⟶ Y) (e : p' = h ≫ p) {m : ℕ} (σ : SecP L p m)
    (x : Sp F ⟶ Y') (τ : L.ι → F) (c : F) : HasVal (pullP h e σ) x τ c ↔ HasVal σ (x ≫ h) τ c := by
  subst e
  unfold HasVal
  rw [Category.assoc]
  refine forall_congr' fun j => forall_congr' fun hj => Eq.congr_left ?_
  have hm : x (pt F) ∈ LB.wchart L (fun _ : Fin 1 => h ≫ p) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (show (h ≫ p) (x (pt F)) ∈ L.U j from mem_of_le hj)
  exact valF_appLE h _ _ (le_of_mem hm) _

theorem hasVal_id {m : ℕ} (s : Out.H0 L m) (x : Sp F ⟶ X) (τ : L.ι → F) (c : F) :
    HasVal (p := 𝟙 X) s x τ c ↔ HasValueAt s x τ c := by
  unfold HasVal
  rw [Category.comp_id]
  rfl

theorem isFrameAt_of_isFrm {x : Sp F ⟶ X} {τ : L.ι → F} (h : IsFrm L x τ) : IsFrameAt L x τ :=
  ⟨fun a ha => (h.1 a ha).ne_zero, fun a b ha hb => h.2 a b (le_of_mem ⟨mem_of_le ha, mem_of_le hb⟩)⟩

theorem inSpan_of_comp {f : X ⟶ Y} {H : LB X} {I K : Type} [Fintype I] [Fintype K] (t : K → LB.Sec H) (e : I → K)
    {s : LB.Sec H} (h : InSpan f (fun a => t (e a)) s) : InSpan f t s := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨fun l => ∑ a, if e a = l then c a else 0, fun k => (hc k).trans ?_⟩
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (e a) (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, zero_mul]) (by simp),
    if_pos rfl]

theorem valF_const (c : F) : valF (𝟙 (Sp F)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = c := by
  rw [valF_eq le_rfl]
  simp [valHom, Scheme.Hom.appLE]

variable {J : Type} {x : J → (Sp F ⟶ X)} {τ : J → L.ι → F}

theorem inSpan_of_values [IsReduced X] (hx : MeetsOpens x) (f : X ⟶ Sp F) (hf : ∀ j, x j ≫ f = 𝟙 _) {N n : ℕ}
    (t : Fin n → Out.H0 L N) (φ : Fin n → J → F) (ht : ∀ a j, HasValueAt (t a) (x j) (τ j) (φ a j)) (r : Fin n → F)
    (u : Out.H0 L N) (hu : ∀ j, HasValueAt u (x j) (τ j) (∑ a, r a * φ a j)) : InSpan f t u := by
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r a), fun k => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = fun _ => b := ⟨k 0, funext fun i => congrArg k (Subsingleton.elim _ _)⟩
  refine hx.fn_ext (U := chart L b) fun j hj => ?_
  have hb : ⊤ ≤ x j ⁻¹ᵁ L.U b := le_of_mem (Set.mem_iInter.1 (mem_of_le hj) 0)
  refine (hu j b hb).trans (Eq.trans ?_ ((valF_eq hj _).trans (map_sum _ _ _)).symm)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm (((valF_eq hj _).symm.trans (valF_mul hj _ _)).trans ?_)
  rw [_root_.mul_assoc]
  exact congrArg₂ (· * ·) ((valF_appLE f ⊤ le_top hj _).trans (by rw [hf]; exact valF_const _)) (ht a j b hb)

theorem embedsBy_of_values [IsReduced X] (hx : MeetsOpens x) (f : X ⟶ Sp F) [UniversallyClosed f]
    (hf : ∀ j, x j ≫ f = 𝟙 _) {N : ℕ} {K I : Type} [Fintype K] {s : K → Out.H0 L N} (hs : EmbedsBy f s)
    (t : I → Out.H0 L N) (φ : I → J → F) (ht : ∀ a j, HasValueAt (t a) (x j) (τ j) (φ a j))
    (hu : ∀ u : Out.H0 L N, ∃ (n : ℕ) (r : Fin n → F) (i : Fin n → I),
      ∀ j, HasValueAt u (x j) (τ j) (∑ a, r a * φ (i a) j)) : EmbedsBy f t := by
  choose n r i hu using hu
  let e : (Σ k, Fin (n (s k))) → I := fun p => i _ p.2
  have hst : ∀ k, InSpan f (fun p => t (e p)) (s k) := fun k => inSpan_of_comp _ (Sigma.mk k)
    (inSpan_of_values hx f hf _ (fun a => φ (i _ a)) (fun a => ht _) _ _ (hu _))
  refine ⟨top_le_iff.1 ((iSup_nonzeroLocus_of_inSpan hs.1 hst).ge.trans
    (iSup_le fun p => le_iSup (fun l => Out.nonzeroLocus (t l)) (e p))), fun l => ?_⟩
  obtain ⟨h₁, h₂⟩ := hs.affine_and_surjective hst (t l)
  choose q hq using fun a => exists_isRatio (t a) (t l)
  refine ⟨h₁, q, hq, fun y => ?_⟩
  obtain ⟨P, rfl⟩ := h₂ (fun p => q (e p)) (fun p => hq _) y
  exact ⟨MvPolynomial.rename e P, MvPolynomial.eval₂Hom_rename _ _ _ _⟩

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {F : Type} [Field F]
  {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F}

section Triple

variable {t : SAB H (Sp F)} (Θ : FPts act t (𝟙 _) φ)

theorem fib_fst (v : V) : fib (Θ.x v) ≫ pullback.fst t.G.hom (𝟙 _) = (Θ.x v).left := pullback.lift_fst _ _ _

theorem x_zero : Θ.x 0 = 1 := mul_eq_left.1 ((Θ.add 0 0).symm.trans (congrArg Θ.x (add_zero 0)))

theorem x_zero_left : (Θ.x 0).left = eSec t.G := by
  rw [x_zero, Hom.one_def, Over.comp_left]
  exact (congrArg (· ≫ _) ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (𝟙 (Sp F))))))).trans
    (Category.id_comp _)

theorem separates : SeparatesSections t.PP.L fun v => (Θ.x v).left := by
  intro m hm u hu a
  have e : pullback.fst t.G.hom (𝟙 _) = pullback.fst t.G.hom (𝟙 _) ≫ 𝟙 _ := (Category.comp_id _).symm
  have h0 := Θ.sep m hm (pullP _ e u) (fun v => (hasVal_pullP _ e u _ _ _).2 (by
    rw [fib_fst, hasVal_id]
    exact fun b hb => (hu v _ (top_le_chart hb)).trans (zero_mul _).symm)) a
  refine fn_ext fun y hy => ?_
  have hz : inv (pullback.fst t.G.hom (𝟙 _)) y ∈
      LB.wchart t.PP.L (fun _ : Fin 1 => pullback.fst t.G.hom (𝟙 _)) a := Set.mem_iInter.2 fun k => by
    show (inv (pullback.fst t.G.hom (𝟙 _)) ≫ pullback.fst t.G.hom (𝟙 _)) y ∈ t.PP.L.U (a k)
    rw [IsIso.inv_hom_id]
    exact Set.mem_iInter.1 hy k
  have := gs_chartSec (chartPullSame t.PP.L _ _ _ _ fun _ => e) u (inv (pullback.fst t.G.hom (𝟙 _))) y a hz
  rw [IsIso.inv_hom_id] at this
  refine this.symm.trans ((congrArg (gs _ y _) h0).trans ?_)
  exact ((gs_eq _ y _ hz _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).trans
    ((gs_eq (𝟙 _) y _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem exists_sections {N : ℕ} (hN : 1 ≤ N) : ∃ s : I N → Out.H0 t.PP.L N,
    (∀ i v, HasValueAt (s i) (Θ.x v).left (Θ.τ v) (φ N i v)) ∧
    ∀ u : Out.H0 t.PP.L N, ∃ (n : ℕ) (r : Fin n → F) (i : Fin n → I N),
      ∀ v, HasValueAt u (Θ.x v).left (Θ.τ v) (∑ a, r a * φ N (i a) v) := by
  refine ⟨fun i => pullP (inv (pullback.fst t.G.hom (𝟙 _))) (IsIso.inv_hom_id _).symm (Θ.sig N i),
    fun i v => ?_, fun u => ?_⟩
  · rw [← hasVal_id, hasVal_pullP, ← fib_fst, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact Θ.val N hN i v
  · obtain ⟨n, r, i, h⟩ := Θ.span N hN (pullP _ (Category.comp_id _).symm u)
    refine ⟨n, r, i, fun v => ?_⟩
    have := (hasVal_pullP _ _ _ _ _ _).1 (h v)
    rwa [fib_fst, hasVal_id] at this

end Triple

variable {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B} {s : Sp F ⟶ Sp B}

theorem exists_embedding (hA : Out.AmpleSt) (o : Obj D l bb s) (Θ : FPts act o.t (𝟙 _) φ) {N : ℕ} (hN : 4 ≤ N) :
    ∃ t : I N → Out.H0 o.t.PP.L N, EmbedsBy o.t.G.hom t ∧
      ∀ i v, HasValueAt (t i) (Θ.x v).left (Θ.τ v) (φ N i v) := by
  obtain ⟨t, ht, hu⟩ := exists_sections Θ (N := N) (by omega)
  have := o.proper
  have : IsIntegral o.t.G.left := isIntegral_left_of_isAbelianScheme_field _ (objPolAV o).isAb
  obtain ⟨M, u, hs⟩ := exists_embedsBy_of_isPullback o.t.G o.t.PP.isLB (hA _ (objPolAV o) N hN).2
    (isAffineOpen_top _) (φ := 𝟙 _) (f' := o.t.G.hom) (g := 𝟙 _ ≫ (Sp F).topIso.inv)
    (by rw [comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  exact ⟨t, embedsBy_of_values (X := o.t.G.left) (meetsOpens_of_separatesSections (objPolAV o) (separates Θ)) o.t.G.hom
    (fun v => Over.w (Θ.x v)) hs t _ ht hu, ht⟩

theorem isRigIso_of_value {G G' : Over (Sp F)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (β : G ⟶ G') [IsMonHom β] (L : RigLB G) (L' : RigLB G') (w : LB.Iso L.L (L'.L.pull β.left)) (hw : w.IsGen)
    (h : ∀ a a', ⊤ ≤ (show Sp F ⟶ _ from eSec G) ⁻¹ᵁ L.L.U a → ⊤ ≤ (show Sp F ⟶ _ from eSec G') ⁻¹ᵁ L'.L.U a' →
      valF (F := F) (eSec G) _ (w.s (fun _ => a', a)).val * valF (𝟙 (Sp F)) _ (L.rig.s fun _ => a).val =
        valF (𝟙 (Sp F)) _ (L'.rig.s fun _ => a').val) : IsRigIso (CubeMap.ofHom β) L L' w := by
  have he : eSec G ≫ β.left = 𝟙 _ ≫ eSec G' := (CubeMap.ofHom β).e_comm
  refine ⟨hw, maps_of_good ((isGen_iff w).1 hw) L'.isLB L.isLB (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec G') (ε := fun _ => 1) L.rig L.rigGen L'.rig L'.rigGen (fun _ => he) fun y J J' hJ hJ' => ?_⟩
  have m := hJ (eSec G ≫ β.left)
  have m' := hJ' (eSec G)
  have m₀ : eSec G' y ∈ L'.L.U (J (eSec G ≫ β.left)) := by
    have := hJ (𝟙 _ ≫ eSec G')
    rw [he]; exact this
  have e := congrArg (toStk (F := F) y) (h _ _ ((top_le_iff_mem (F := F) _ _ y).2 m')
    ((top_le_iff_mem (F := F) _ _ y).2 m₀))
  rw [val_of _ _ y J (fun _ => J (eSec G ≫ β.left)) (fun _ => congrArg J he.symm),
    val_of _ _ y J' (fun _ => J' (eSec G)) (fun _ => congrArg J' (Category.id_comp _)), Fintype.prod_unique, zpow_one]
  refine Units.ext ((toStk_valF (F := F) (𝟙 _) _ y (mem_pull.2 m₀) _).symm.trans (e.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (toStk_valF (F := F) (𝟙 _) _ y (mem_pull.2 m') _)))))
  exact toStk_valF (F := F) (eSec G) ((L'.L.pull β.left).U (fun _ => J (eSec G ≫ β.left)) ⊓ L.L.U (J' (eSec G))) y
    ⟨mem_pull.2 m, m'⟩ _

theorem exists_sabMap_of_same_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ), ∃ (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)), IsRigIso m.cm o₁.t.PP o₂.t.PP w ∧ ∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j' := by
  intro hL _ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ s o₁ o₂ Θ₁ Θ₂
  obtain ⟨s₁, e₁, v₁⟩ := exists_embedding hL.ample o₁ Θ₁ (N := 4) le_rfl
  obtain ⟨s₂, e₂, v₂⟩ := exists_embedding hL.ample o₂ Θ₂ (N := 4) le_rfl
  obtain ⟨t₁, e₁', v₁'⟩ := exists_embedding hL.ample o₁ Θ₁ (N := 5) (by norm_num)
  obtain ⟨t₂, e₂', v₂'⟩ := exists_embedding hL.ample o₂ Θ₂ (N := 5) (by norm_num)
  have f₁ := fun v => isFrameAt_of_isFrm (Θ₁.frm v)
  have f₂ := fun v => isFrameAt_of_isFrm (Θ₂.frm v)
  have d₁ := separates Θ₁
  have d₂ := separates Θ₂
  obtain ⟨β, hβ⟩ : ∃ β : o₁.t.G ⟶ o₂.t.G, ∀ v, Θ₁.x v ≫ β = Θ₂.x v :=
    exists_over_hom (P := objPolAV o₁) (P' := objPolAV o₂) f₁ f₂ s₁ s₂ e₁ e₂ (fun i v => ⟨_, v₁ i v, v₂ i v⟩) d₁
  obtain ⟨δ, hδ⟩ : ∃ δ : o₂.t.G ⟶ o₁.t.G, ∀ v, Θ₂.x v ≫ δ = Θ₁.x v :=
    exists_over_hom (P := objPolAV o₂) (P' := objPolAV o₁) f₂ f₁ s₂ s₁ e₂ e₁ (fun i v => ⟨_, v₂ i v, v₁ i v⟩) d₂
  have ext : ∀ (o o' : Obj D l bb s) (Θ : FPts act o.t (𝟙 _) φ) (f g : o.t.G ⟶ o'.t.G),
      (∀ v, Θ.x v ≫ f = Θ.x v ≫ g) → f = g := fun o o' Θ f g h =>
    hom_ext_of_separatesSections (objPolAV o) (objPolAV o') (separates Θ) h
  let ψ : o₁.t.G ≅ o₂.t.G := ⟨β, δ,
    ext _ _ Θ₁ _ _ fun v => by rw [← Category.assoc, hβ, hδ, Category.comp_id],
    ext _ _ Θ₂ _ _ fun v => by rw [← Category.assoc, hδ, hβ, Category.comp_id]⟩
  have hm : IsMonHom β := hL.rigidity _ _ _ (objPolAV o₁).isAb (objPolAV o₂).isAb β (by
    have e : (Θ₁.x 0).left ≫ β.left = (Θ₂.x 0).left := congrArg CommaMorphism.left (hβ 0)
    rw [x_zero_left, x_zero_left] at e
    exact Over.OverMorphism.ext e)
  have : IsMonHom ψ.hom := hm
  have a₁ : IsAbelianScheme o₁.t.G := (objPolAV o₁).isAb
  have hact : ∀ a, o₁.t.act.act a ≫ β = β ≫ o₂.t.act.act a := fun a => ext _ _ Θ₁ _ _ fun v => by
    rw [← Category.assoc, ← Θ₁.lin, hβ, ← Category.assoc, hβ, Θ₂.lin]
  have hx : ∀ v, (Θ₁.x v).left ≫ β.left = (Θ₂.x v).left := fun v => congrArg CommaMorphism.left (hβ v)
  have : IsIntegral o₁.t.G.left := isIntegral_left_of_isAbelianScheme_field _ (objPolAV o₁).isAb
  obtain ⟨w, hw, hv⟩ := (meetsOpens_of_separatesSections (objPolAV o₁) d₁).exists_lbIso (X := o₁.t.G.left)
    (x' := fun v => (Θ₂.x v).left) β.left hx f₁ f₂ rfl s₁ s₂ t₁ t₂ e₁.1 e₂.1 e₁'.1 e₂'.1
    (fun i v => ⟨_, v₁ i v, v₂ i v⟩) (fun i v => ⟨_, v₁' i v, v₂' i v⟩)
  refine ⟨⟨CubeMap.ofHom β, isGrpPullback_of_iso ψ, rfl, fun a => congrArg CommaMorphism.left (hact a),
    HeckePoint.isPullCubical_of_iso hL.globalFns a₁ β o₁.t.cub o₂.t.cub ⟨w, hw⟩⟩, w,
    ?_, fun v => ⟨hx v, fun j j' hj => ?_⟩⟩
  · refine isRigIso_of_value (G := o₁.t.G) (G' := o₂.t.G) β o₁.t.PP o₂.t.PP w hw fun a a' ha ha' => ?_
    rw [← x_zero_left Θ₁] at ha
    rw [← x_zero_left Θ₂] at ha'
    have e := hv 0 a a' ha ha'
    rw [Θ₁.rig a ha, Θ₂.rig a' ha', x_zero_left] at e
    exact e
  · have hj' := mem_of_le hj
    refine (hv v j' j (le_of_mem hj'.2) ?_).symm
    rw [← hx]
    exact le_of_mem (x := (Θ₁.x v).left ≫ β.left) (mem_pull.1 hj'.1)

end GlobalTheory.FamilyIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRepresents
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpTan

open GlobalTheory.HolHom GlobalTheory.TorusModel

theorem le_wchart_iff {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (x : Z ⟶ Y)
    (j : K → L.ι) : ⊤ ≤ LB.wchart L (fun k => x ≫ ψ k) j ↔ ⊤ ≤ x ⁻¹ᵁ LB.wchart L ψ j :=
  ⟨fun h _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k,
    fun h _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k⟩

theorem valR_of_corr {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Sp A ⟶ X)} {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {t : LB.Gen (LB.LinComb L ψ ε)} (ht : t.IsGen) (x : Sp A ⟶ Y) (hφ : φ = fun k => x ≫ ψ k)
    (h : LB.Gen.Corr L _ _ _ _ u (LB.pullGen L _ _ t x)) (j : K → L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart L φ j) (u.s j).val = valR x (LB.wchart L ψ j) (t.s j).val := by
  subst hφ
  obtain rfl := TorusCoord.gen_eq_of_corr hL hu (DVR.pullGen_isGen _ _ _ _ ht x) h
  by_cases hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ψ j
  · have hj' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => x ≫ ψ k) j := (le_wchart_iff L ψ x j).2 hj
    refine (valR_res (U := x ⁻¹ᵁ LB.wchart L ψ j) (𝟙 (Sp A)) _ _ hj').trans ?_
    exact (valR_comp (𝟙 (Sp A)) x (LB.wchart L ψ j) _).symm.trans (by rw [Category.id_comp])
  · have h₀ : valR x (LB.wchart L ψ j) (t.s j).val = 0 := dif_neg hj
    exact (dif_neg (fun h => hj ((le_wchart_iff L ψ x j).1 h))).trans h₀.symm

section Coord

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : GtCoord I D e G)
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

open CoordToExt in

theorem holAt_of_coord {x : V → (Sp ℂ ⟶ (thickObj R I e G).left)} {z : V}
    (hb : HolAt (fun t => x t ≫ c.q.left) z)
    (hs : ∀ χ a, ⊤ ≤ x z ⁻¹ᵁ LB.wchart D.P.L (D.Oφ c.pG χ) a →
      DifferentiableAt ℂ (fun t => valAt' (x t) (LB.wchart D.P.L (D.Oφ c.pG χ) a) ((c.t χ).s a).val) z) :
    HolAt x z := by
  let b := Module.Free.chooseBasis ℤ D.X
  let p := (x z ≫ c.q.left) (default : PrimeSpectrum ℂ)
  choose a ha using fun k => exists_chart (DVR.linComb_isLB (Y := (thickObj R I e D.P.A).left) D.P.L D.P.isLB
    (D.Oφ (D.prBe I e) (b k)) Oε) p
  have hW : ⊤ ≤ (x z ≫ c.q.left) ⁻¹ᵁ ⨅ k, (bundle I D e (b k)).U (a k) := by
    rw [le_preimage_iff, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.2 ha
  obtain ⟨P, hP, hxP, hle⟩ := exists_affine _ hW
  have hl : ∀ k, c.q.left ⁻¹ᵁ P ≤ c.q.left ⁻¹ᵁ (bundle I D e (b k)).U (a k) := fun k =>
    Scheme.Hom.preimage_mono _ (hle.trans (iInf_le _ k))
  let u : ∀ k, Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P)ˣ := fun k => res (hl k) (coordUnit c (b k) (a k))
  have := c.q_hom
  have := c.q_affine
  have bij := bijective_of_basis b c.q c.i c.q_hom c.i_hom c.q_flat c.q_surj c.q_affine c.isKernel P hP u
    (fun k Z t g w hw => by
      have hw' := GtBaseChange.translate_mem c.q c.i c.isKernel t g P w hw
      exact (gm_res _ w (hl k) hw' _).trans ((coordUnit_weight c (b k) (a k) Z t g w (hl k hw)).trans
        (congrArg _ (gm_res _ w (hl k) hw _).symm)))
  have ev : ∀ᶠ t in 𝓝 z, ⊤ ≤ x t ⁻¹ᵁ (c.q.left ⁻¹ᵁ P) := (hb P hxP).1
  let S : Subring Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P) :=
    { carrier := {f | DifferentiableAt ℂ (fun t => valAt' (x t) _ f) z}
      mul_mem' := fun {f f'} h h' => (h.mul h').congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_mul, Pi.mul_apply])
      add_mem' := fun {f f'} h h' => (h.add h').congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_add, Pi.add_apply])
      neg_mem' := fun {f} h => h.neg.congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_neg, Pi.neg_apply])
      one_mem' := (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_one])
      zero_mem' := (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_zero]) }
  have hu : ∀ k, (u k).val ∈ S := fun k => by
    have h₁ := hs (b k) (a k) (fun y hy => mem_chart c _ _ _ (hl k (hxP hy)))
    refine h₁.congr_of_eventuallyEq (ev.mono fun t ht => ?_)
    exact (valR_res (x t) (hl k) _ ht).trans (valR_res (x t) _ _ (fun y hy => hl k (ht hy)))
  have hi : ∀ w : Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P)ˣ, w.val ∈ S → (w⁻¹).val ∈ S := fun w hw => by
    have hne : valAt' (x z) _ w.val ≠ 0 := by
      rw [valAt'_eq_valR, valR_eq (x z) (c.q.left ⁻¹ᵁ P) hxP]
      exact (w.isUnit.map _).ne_zero
    refine (DifferentiableAt.inv hw hne).congr_of_eventuallyEq (ev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, Pi.inv_apply, map_units_inv]
  refine holAt_of_affine (hP.preimage c.q.left) hxP ev fun f => ?_
  obtain ⟨f, rfl⟩ := bij.2 f
  change _ ∈ S
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f f' h h' => rw [map_add]; exact add_mem h h'
  | single χ r =>
    have hχ : ∀ χ : D.X, ((b.constr ℤ (fun k => Additive.ofMul (u k)) χ).toMul).val ∈ S := fun χ => by
      have : χ ∈ Submodule.span ℤ (Set.range b) := b.mem_span χ
      induction this using Submodule.span_induction with
      | mem _ h => obtain ⟨k, rfl⟩ := h; rw [b.constr_basis]; exact hu k
      | zero => rw [map_zero]; exact one_mem _
      | add _ _ _ _ h h' => rw [map_add]; exact mul_mem h h'
      | smul n w _ h =>
        rw [map_smul, toMul_zsmul]
        cases n with
        | ofNat n => simpa using pow_mem h n
        | negSucc n => rw [zpow_negSucc]; exact hi _ (by simpa using pow_mem h (n + 1))
    rw [AddMonoidAlgebra.liftNCRingHom_single]
    refine mul_mem ?_ (hχ χ)
    exact ((hb P hxP).2 r).congr_of_eventuallyEq (Eventually.of_forall fun t => (valR_comp (x t) c.q.left P r).symm)

end Coord

theorem exists_represents {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Spec (CommRingCat.of R))}
    [GrpObj H] [IsCommMonObj H] (hG : GlobalFnsSt) (c : GtCoord ⊥ D 0 H) :
    ∃ Φ : ∀ T, (T ⟶ H) ≃ GtPt D T, Represents Φ ∧
      ∀ T (x : T ⟶ H), TorusCoord.IsPointOf c (x.left ≫ inv (fstG (⊥ : Ideal R) 0 H).left) (Φ T x) := by
  let j := inv (fstG (⊥ : Ideal R) 0 H).left
  have hj : j ≫ (thickObj R ⊥ 0 H).hom ≫ thick R ⊥ 0 = H.hom :=
    (congrArg (j ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H)).symm).trans (IsIso.inv_hom_id_assoc _ _)
  choose φ hφ using fun T (x : T ⟶ H) => TorusCoord.exists_isPointOf c (T := T) (x.left ≫ j)
    (by rw [Category.assoc, hj, Over.w])
  have bij : ∀ T, Function.Bijective (φ T) := fun T => by
    refine ⟨fun x x' e => Over.OverMorphism.ext ((cancel_mono j).1
      ((hφ T x).unique_left c (e ▸ hφ T x'))), fun ξ => ?_⟩
    obtain ⟨y, hy⟩ := TorusCoord.exists_point c (T.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
    refine ⟨Over.homMk (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ((Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H))).trans (hy.comp_hom c))), (hφ T _).unique_right c ?_⟩
    have : (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ≫ j = y := by simp [j]
    exact this.symm ▸ hy
  refine ⟨fun T => Equiv.ofBijective _ (bij T), ⟨fun T' T k x => (hφ T x).isPull c ?_, fun T x x' => ?_⟩, hφ⟩
  · have := hφ T' (k ≫ x)
    rwa [Over.comp_left, Category.assoc] at this
  · obtain ⟨T, ⟨⟨⟩⟩, s⟩ := T
    change T ⟶ Spec (CommRingCat.of R) at s
    obtain ⟨σ, rfl⟩ : ∃ σ, s = σ ≫ thick R ⊥ 0 := ⟨s ≫ inv (thick R ⊥ 0), by simp⟩
    let Z : Over (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) := Over.mk σ
    obtain ⟨a, ha⟩ := FormalPoint.exists_lift_fstG (Z := Z) x
    obtain ⟨a', ha'⟩ := FormalPoint.exists_lift_fstG (Z := Z) x'
    have key : ∀ (b : Z ⟶ thickObj R ⊥ 0 H) (w : (Over.map (thick R ⊥ 0)).obj Z ⟶ H),
        (Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H = w → φ _ w = TorusCoord.pointsEquiv c Z b := by
      rintro b _ rfl
      refine ((TorusCoord.toGtPt_eq_iff c b _).2 ?_).symm
      have e : ((Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H).left ≫ j = b.left := by
        rw [Over.comp_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]; rfl
      exact e ▸ hφ _ _
    have e₁ := key a x ha
    have e₂ := key a' x' ha'
    have e₃ := key (a * a') (x * x') (by rw [FormalPoint.map_mul_fstG, ha, ha'])
    have := TorusCoord.isAdd_pointsEquiv c hG a a'
    rw [← e₁, ← e₂, ← e₃] at this
    exact this

theorem exists_model (hG : GlobalFnsSt) (D : DegPre ℂ) :
    ∃ (H : Over (Sp ℂ)) (_ : GrpObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), Smooth H.hom ∧ Represents Φ ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (y : Sp ℂ ⟶ Sp ℂ) (e : V → (Over.mk y ⟶ H)) (z : V),
        HolAt (fun t => (show Sp ℂ ⟶ _ from (Φ _ (e t)).b.left)) z →
        (∀ χ j, ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ (e z)).b χ) j → DifferentiableAt ℂ (fun t =>
          valR (A := ℂ) (𝟙 _) (LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ (e t)).b χ) j)
            (((Φ _ (e t)).s χ).s j).val) z) →
        HolAt (fun t => (show Sp ℂ ⟶ _ from (e t).left)) z := by
  obtain ⟨H, _, _, h⟩ := exists_isGt hG (splitExt D)
  obtain ⟨c⟩ := nonempty_gtCoord hG h ⊥ 0
  obtain ⟨Φ, h₁, h₂⟩ := exists_represents hG c
  refine ⟨H, inferInstance, Φ, (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ H h).1, h₁, fun V _ _ y e z hb hs => ?_⟩
  let j := inv (fstG (⊥ : Ideal ℂ) 0 H).left
  have hφ : ∀ t χ, DegPre.gtφT D _ (Φ _ (e t)).b χ = fun k => ((e t).left ≫ j) ≫ D.Oφ c.pG χ k := fun t χ =>
    funext fun k => (Category.id_comp _).symm.trans ((TorusCoord.comp_eq_of_left (Φ _ (e t)).b c.pG (𝟙 _)
      ((e t).left ≫ j) ((Category.id_comp _).trans (h₂ _ (e t)).1)).1 χ k)
  have H₁ : HolAt (fun t => (show Sp ℂ ⟶ _ from (e t).left ≫ j)) z := by
    refine holAt_of_coord c ?_ fun χ a ha => ?_
    · have := hb.comp (inv (fstG (⊥ : Ideal ℂ) 0 D.P.A).left)
      refine (congrArg (fun q => HolAt q z) (funext fun t => ?_)).mp this
      exact ((IsIso.eq_comp_inv (fstG (⊥ : Ideal ℂ) 0 D.P.A).left).2
        ((h₂ _ (e t)).1.trans (Category.assoc _ _ _).symm).symm).symm
    · have := hs χ a (by rw [hφ]; exact (le_wchart_iff _ _ _ a).2 ha)
      convert this using 2 with t
      exact (valR_of_corr (A := ℂ) D.P.isLB ((Φ _ (e t)).isGen χ) (c.t_gen χ) _ (hφ t χ) ((h₂ _ (e t)).2 χ) a).symm
  have := H₁.comp (fstG (⊥ : Ideal ℂ) 0 H).left
  convert this using 2 with t
  simp [j]

end GlobalTheory.ExpTan
end
end

