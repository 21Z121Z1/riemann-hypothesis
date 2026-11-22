import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDefiniteSpaceIsometryOfAdaptedPair
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.IndIsom
variable {K V W : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {H : HermSpace K V} {r : ℕ}

theorem perpX (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) :
    ∀ x ∈ F.X, H.B x v = 0 := by
  have h : F.X ≤ LinearMap.ker (H.B.flip v) := by
    rw [FlagD.X, FlagD.Xa, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  intro x hx
  simpa using h hx

theorem map_mem {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hG : ∀ a, G.e a = γ (F.e a)) {x : V} (hx : x ∈ F.X) :
    γ x ∈ G.X := by
  have h : F.X.map (γ : V →ₗ[K] V) = G.X := by
    simp only [FlagD.X, FlagD.Xa, Submodule.map_span, Set.image_image, hG, LinearEquiv.coe_coe]
  rw [← h]
  exact Submodule.mem_map_of_mem hx

theorem mem_of_map {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hG : ∀ a, G.e a = γ (F.e a)) {x : V} (hx : γ x ∈ G.X) :
    x ∈ F.X := by
  have h := map_mem (F := G) (G := F) (γ := γ.symm)
    (fun a => by rw [hG a, LinearEquiv.symm_apply_apply]) hx
  rwa [LinearEquiv.symm_apply_apply] at h

theorem B_mod {S : Submodule K V} {u u' y y' : V} (hu : ∀ x ∈ S, H.B x u = 0) (hy' : ∀ x ∈ S, H.B x y' = 0)
    (h : y - u ∈ S) (h' : y' - u' ∈ S) : H.B y y' = H.B u u' := by
  have h1 : H.B (y - u) y' = 0 := hy' _ h
  have h2 : H.B (y' - u') u = 0 := hu _ h'
  have h3 : H.B u (y' - u') = 0 := by rw [← H.herm, h2, star_zero]
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
  rw [map_sub, sub_eq_zero] at h3
  rw [h1, h3]

end GlobalTheory.DegAsm.IndIsom

namespace GlobalTheory.DegAsm
open IndIsom
private lemma sup_iff_lemma {K V : Type} [Field K] [AddCommGroup V] [Module K V] {R : Type} [CommRing R]
    [Algebra R K] [Module R V] [IsScalarTower R K V] (M : Submodule R V) (S : Submodule K V) {a b : V}
    (h : a - b ∈ S) : a ∈ M ⊔ S.restrictScalars R ↔ b ∈ M ⊔ S.restrictScalars R := by
  have h' : a - b ∈ M ⊔ S.restrictScalars R := Submodule.mem_sup_right h
  constructor
  · intro ha
    simpa using sub_mem ha h'
  · intro hb
    simpa using add_mem hb h'

theorem exists_isH : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (γ : V ≃ₗ[K] V), IsEmb F HW e → Adapt F G 𝔡 N → γ ∈ isomGrp H → (∀ a, G.e a = γ (F.e a)) → ∃ h : W ≃ₗ[K] W, h ∈ isomGrp HW ∧ IsH F G e γ h ∧ (∀ h' : W ≃ₗ[K] W, IsH F G e γ h' → h' = h) ∧ ∀ (g : ℕ) (Λ' : Submodule (𝓞 K) V), (datOf F G e g (γ • Λ')).1 = imLat h (lat0 F e Λ') := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hCM r F G 𝔡 N γ hE hAd hγ hG
  classical
  obtain ⟨-, hXF, hXG, hV0, -⟩ := adapt_invariants K V H hCM r F G 𝔡 N hAd
  obtain ⟨hfull, -⟩ := NF.geometry K V H hCM r N
  obtain ⟨-, -, -, -, -, hIF, hIG, -, hexG⟩ := hfull
  simp only [II, hXF, hXG, hV0] at hIF hIG hexG
  have hW : ∀ y, y ∈ wSp F G ↔ ∀ v ∈ V0 F G, H.B v y = 0 := fun y =>
    GlobalTheory.DegCnt.NFGeom.mem_perp' (H := H) (V0 F G) y
  have hFV0 : F.X ≤ V0 F G := le_sup_left.trans le_sup_left
  have hGV0 : G.X ≤ V0 F G := le_sup_right.trans le_sup_left
  have hzF : F.z ∈ V0 F G := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  have feV0 : ∀ a : Fin (r + 1), F.e a ∈ V0 F G := by
    intro a
    induction a using Fin.lastCases with
    | last => exact hzF
    | cast b => exact hFV0 (Submodule.subset_span ⟨b, b.isLt, rfl⟩)
  have hA : ∀ x ∈ F.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ G.X := fun x hx hv =>
    (Submodule.mem_inf.mp ((hIF x hx).1 hv)).2
  have hB : ∀ x ∈ G.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ F.X := fun x hx hv =>
    (Submodule.mem_inf.mp ((hIG x hx).1 hv)).1
  have hSG : SameGr G N.F' := hAd.2.2
  have hC : ∀ w, (∀ a, H.B (G.e a) w = 0) → ∃ x ∈ G.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0 := by
    intro w hw
    apply hexG
    intro a
    have h1 : N.F'.e a - G.e a ∈ G.X := AdaptInv.xa_mono G (Nat.lt_succ_iff.mp a.isLt) (hSG a)
    have h2 := perpX G hw _ h1
    rw [map_sub, LinearMap.sub_apply, hw a, sub_zero] at h2
    exact h2
  have hEperp : ∀ u : W, ∀ a, H.B (F.e a) (e u) = 0 := fun u =>
    (hE.2 (e u)).2 (Submodule.mem_sup_left (LinearMap.mem_range_self e u))
  have hEX : ∀ u : W, ∀ x ∈ F.X, H.B x (e u) = 0 := fun u => perpX F (hEperp u)
  have hγB := (mem_isomGrp H γ).1 hγ
  have hγperp : ∀ u : W, ∀ a, H.B (G.e a) (γ (e u)) = 0 := fun u a => by
    rw [hG a, hγB]; exact hEperp u a
  have hγX : ∀ u : W, ∀ x ∈ G.X, H.B x (γ (e u)) = 0 := fun u => perpX G (hγperp u)
  have heX : ∀ u : W, e u ∈ F.X → u = 0 := by
    intro u hu
    apply HW.nondeg u
    intro u'
    rw [← hE.1]
    exact hEX u' _ hu
  have hex : ∀ w : W, ∃ u : W, ∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X := by
    intro w
    obtain ⟨x, hxG, hx⟩ := hC (γ (e w)) (hγperp w)
    have hy : γ (e w) - x ∈ wSp F G := (hW _).2 hx
    have hyF : ∀ a, H.B (F.e a) (γ (e w) - x) = 0 := fun a => hx _ (feV0 a)
    obtain ⟨y1, hy1, z, hz, hyz⟩ := Submodule.mem_sup.mp ((hE.2 _).1 hyF)
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hy1
    refine ⟨u, γ (e w) - x, hy, ?_, ?_⟩
    · rw [← hyz]; simpa using hz
    · simpa using neg_mem hxG
  have huniq : ∀ w u₁ u₂, (∃ y ∈ wSp F G, y - e u₁ ∈ F.X ∧ y - γ (e w) ∈ G.X) →
      (∃ y ∈ wSp F G, y - e u₂ ∈ F.X ∧ y - γ (e w) ∈ G.X) → u₁ = u₂ := by
    rintro w u₁ u₂ ⟨y₁, hy₁, hF₁, hG₁⟩ ⟨y₂, hy₂, hF₂, hG₂⟩
    have hdG : y₁ - y₂ ∈ G.X := by
      convert sub_mem hG₁ hG₂ using 1; abel
    have hdF : y₁ - y₂ ∈ F.X := hB _ hdG ((hW _).1 (sub_mem hy₁ hy₂))
    have he : e (u₁ - u₂) ∈ F.X := by
      convert add_mem (sub_mem hdF hF₁) hF₂ using 1
      rw [map_sub]; abel
    exact sub_eq_zero.mp (heX _ he)
  choose f hf using hex
  have hchar : ∀ w u, (∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X) → f w = u :=
    fun w u hu => huniq w _ _ (hf w) hu
  have hadd : ∀ w₁ w₂, f (w₁ + w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    apply hchar
    obtain ⟨y₁, hy₁, hF₁, hG₁⟩ := hf w₁
    obtain ⟨y₂, hy₂, hF₂, hG₂⟩ := hf w₂
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_, ?_⟩
    · convert add_mem hF₁ hF₂ using 1; rw [map_add]; abel
    · convert add_mem hG₁ hG₂ using 1; rw [map_add, map_add]; abel
  have hsmul : ∀ (c : K) (w : W), f (c • w) = c • f w := by
    intro c w
    apply hchar
    obtain ⟨y, hy, hF, hGG⟩ := hf w
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_, ?_⟩
    · convert Submodule.smul_mem _ c hF using 1; rw [map_smul, smul_sub]
    · convert Submodule.smul_mem _ c hGG using 1; rw [map_smul, map_smul, smul_sub]
  let fl : W →ₗ[K] W :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun c w => by rw [RingHom.id_apply]; exact hsmul c w }
  have hiso : ∀ w₁ w₂, HW.B (f w₁) (f w₂) = HW.B w₁ w₂ := by
    intro w₁ w₂
    obtain ⟨y₁, hy₁, hF₁, hG₁⟩ := hf w₁
    obtain ⟨y₂, hy₂, hF₂, hG₂⟩ := hf w₂
    rw [← hE.1, ← hE.1]
    have e₁ : H.B y₁ y₂ = H.B (e (f w₁)) (e (f w₂)) :=
      B_mod (S := F.X) (hEX (f w₁)) (fun x hx => (hW y₂).1 hy₂ x (hFV0 hx)) hF₁ hF₂
    have e₂ : H.B y₁ y₂ = H.B (γ (e w₁)) (γ (e w₂)) :=
      B_mod (S := G.X) (hγX w₁) (fun x hx => (hW y₂).1 hy₂ x (hGV0 hx)) hG₁ hG₂
    rw [← e₁, e₂, hγB]
  have hinj : Function.Injective fl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply HW.nondeg w
    intro w'
    have hw0 : f w = 0 := hw
    rw [← hiso w w', hw0, map_zero, LinearMap.zero_apply]
  set h := LinearEquiv.ofInjectiveEndo fl hinj with hh
  have hcoe : ∀ w, h w = f w := fun w => by
    rw [hh, LinearEquiv.coe_ofInjectiveEndo]; rfl
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · rw [mem_isomGrp]
    intro x y
    rw [hcoe, hcoe, hiso]
  · intro w
    rw [hcoe]
    exact hf w
  · intro h' hh'
    ext w
    rw [hcoe]
    exact (hchar w (h' w) (hh' w)).symm
  · intro g Λ'
    ext u
    obtain ⟨w, rfl⟩ : ∃ w, h w = u := ⟨h.symm u, h.apply_symm_apply u⟩
    obtain ⟨y, hy, hF, hGG⟩ := hf w
    rw [← hcoe] at hF
    have hR : h w ∈ imLat h (lat0 F e Λ') ↔ e w ∈ Λ' ⊔ rs (𝓞 K) F.X := by
      simp only [imLat, Formalism.HermitianLatticesTheory.gmap, lat0, Submodule.mem_map, Submodule.mem_comap,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨w', hw', hww⟩
        rwa [h.injective hww] at hw'
      · intro hw
        exact ⟨w, hw, rfl⟩
    have hL : h w ∈ (datOf F G e g (γ • Λ')).1 ↔
        e (h w) ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X := Iff.rfl
    rw [hL, hR, ← sup_iff_lemma _ _ hF]
    have hV0c : V0 G F = V0 F G := by
      simp only [V0]
      rw [sup_comm G.X F.X, Set.pair_comm]
    have hWc : ∀ v, v ∈ wSp G F ↔ v ∈ wSp F G := fun v => by
      simp only [wSp, hV0c]
    have hS2 : y ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X ↔ y ∈ γ • Λ' ⊔ rs (𝓞 K) G.X := by
      constructor
      · intro hy'
        obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp hy'
        have hl1 : l ∈ γ • Λ' ⊔ rs (𝓞 K) G.X := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hl).1).2
        have hl2 : l ∈ wSp F G := (hWc l).1 (Submodule.mem_inf.mp hl).2
        have hx' : x ∈ G.X := by
          have hxy : x = y - l := by rw [← hlx]; abel
          apply hA x hx
          rw [hxy]
          exact (hW _).1 (sub_mem hy hl2)
        rw [← hlx]
        exact add_mem hl1 (Submodule.mem_sup_right hx')
      · intro hy'
        apply Submodule.mem_sup_left
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, hy'⟩, (hWc y).2 hy⟩
        show y ∈ uPerp G F
        rw [uPerp, GlobalTheory.DegCnt.NFGeom.mem_perp']
        intro x hx
        apply (hW y).1 hy
        exact sup_le hGV0 hFV0 hx
    rw [hS2, sup_iff_lemma _ _ hGG]
    constructor
    · intro h1
      obtain ⟨m, hm, x, hx, hmx⟩ := Submodule.mem_sup.mp h1
      obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
      rw [LinearEquiv.smul_def] at hmx
      have hx' : γ (e w - l) ∈ G.X := by
        rw [map_sub, ← hmx]; simpa using hx
      have : e w - l ∈ F.X := IndIsom.mem_of_map hG hx'
      have hsum : e w = l + (e w - l) := by abel
      rw [hsum]
      exact add_mem (Submodule.mem_sup_left hl) (Submodule.mem_sup_right this)
    · intro h1
      obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp h1
      rw [← hlx, map_add]
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (IndIsom.map_mem hG hx))
      rw [← LinearEquiv.smul_def]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hl

end GlobalTheory.DegAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesTermsOrbitsLocal
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.GlobalOrbits

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem mem_rat {n : ℕ}
    {K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ A.rat K) : ∀ p, ∃ g' ∈ K p, A.Ext p g g' := hg

theorem lrel_equivalence (G : GFrames A r k) : Equivalence G.LRel := by
  refine ⟨fun Λ => ⟨1, G.St.one_mem, ?_⟩, ?_, ?_⟩
  · ext x; simp
  · rintro Λ Λ' ⟨g, hg, rfl⟩
    refine ⟨g⁻¹, G.St.inv_mem hg, ?_⟩
    rw [← Submodule.map_comp]
    ext x; simp
  · rintro a b c ⟨g, hg, rfl⟩ ⟨g2, hg2, rfl⟩
    refine ⟨g2 * g, G.St.mul_mem hg2 hg, ?_⟩
    rw [← Submodule.map_comp]
    rfl

theorem drel_equivalence (G : GFrames A r k) : Equivalence G.DRel := by
  refine ⟨fun d => ⟨1, fun p => ⟨1, (G.S p).H0.one_mem, fun _ => rfl, one_smul _ _⟩⟩, ?_, ?_⟩
  · rintro d d' ⟨g, hg⟩
    refine ⟨g⁻¹, fun p => ?_⟩
    obtain ⟨g', h0, he, hd⟩ := hg p
    refine ⟨g'⁻¹, (G.S p).H0.inv_mem h0, fun x => ?_, ?_⟩
    · have h := he (g.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      change g'.symm (A.bc p x) = A.bc p (g.symm x)
      rw [← h, LinearEquiv.symm_apply_apply]
    · rw [← hd, inv_smul_smul]
  · rintro a b c ⟨g, hg⟩ ⟨g2, hg2⟩
    refine ⟨g2 * g, fun p => ?_⟩
    obtain ⟨g', h0, he, hd⟩ := hg p
    obtain ⟨g2', h20, he2, hd2⟩ := hg2 p
    refine ⟨g2' * g', (G.S p).H0.mul_mem h20 h0, fun x => ?_, ?_⟩
    · change g2' (g' (A.bc p x)) = A.bc p (g2 (g x))
      rw [he x, he2 (g x)]
    · rw [mul_smul, hd, hd2]

theorem local_of_lrel (G : GFrames A r k) {Γ Γ' : G.Lt} (h : G.LRel Γ Γ') :
    ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ' = h • A.lat p Γ := by
  obtain ⟨g, hg, rfl⟩ := h
  intro p
  obtain ⟨g', hg', he⟩ := mem_rat hg p
  exact ⟨g', hg', (RatExt.rational_extend A _ p).2.2.2.1 g g' Γ he⟩

end GlobalTheory.HL.GlobalOrbits

namespace GlobalTheory.HL.GlobalOrbits

theorem smul_eq_of_le {F' E' : Type} [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [CommRing E']
    [Algebra F' E'] [TopologicalSpace E'] (L : LocE F' E') {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E')
    (Λ : Submodule L.O (Fin n → E')) (hΛ : IsSD L Hm Λ) (u : (Fin n → E') ≃ₗ[E'] (Fin n → E'))
    (hu : u ∈ isomG L Hm) (hle : ∀ x ∈ Λ, u x ∈ Λ) : u • Λ = Λ := by
  have hu' : ∀ x y, hf L Hm (u x) (u y) = hf L Hm x y := hu
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    exact hle x hx
  · intro hy
    have h1 : u.symm y ∈ Λ := by
      refine (hΛ.2 _).1 fun x hx => ?_
      have := hu' x (u.symm y)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact (hΛ.2 y).2 hy (u x) (hle x hx)
    have h2 : y = u • u.symm y := by simp
    rw [h2]
    exact Submodule.smul_mem_pointwise_smul _ _ _ h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem lrel_of_local (G : GFrames A r k) {d : G.Dat} {Γ Γ' : G.Lt} (hT : G.IsTerm d Γ)
    (hL' : Submodule.IsLattice E Γ') (H : ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ' = h • A.lat p Γ) :
    G.LRel Γ Γ' := by
  have recΓ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ hT.1
  have recΓ' := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ' hL'
  let n : ∀ p, (G.S p).GLV := fun p => if A.lat p Γ' = A.lat p Γ then 1 else (H p).choose
  have hn : ∀ p, n p ∈ (G.S p).St ∧ A.lat p Γ' = n p • A.lat p Γ := by
    intro p
    by_cases hp : A.lat p Γ' = A.lat p Γ
    · simp only [n, if_pos hp]; exact ⟨(G.S p).St.one_mem, by rw [one_smul]; exact hp⟩
    · simp only [n, if_neg hp]; exact (H p).choose_spec
  have hfin : {p | n p ∉ (G.S p).K0}.Finite := by
    refine (recΓ.2.2.union recΓ'.2.2).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hp
    have : A.lat p Γ' = A.lat p Γ := by rw [hc.1, hc.2]
    simp only [n, if_pos this]
    exact (G.S p).K0.one_mem
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ,
      ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (((fun _ => 1 : ∀ p, ((A.loc p).Fp)ˣ) p) : (A.loc p).Fp)}.Finite :=
    Set.finite_empty.subset fun p hp => hp ⟨1, by simp⟩
  obtain ⟨g, hg, hgp⟩ := GlobalTheory.T.exists_mem_St_approximating_local_elements A r k G Γ hT.1 (fun _ => 1) hc n (fun p => (hn p).1) hfin
  have hloc : ∀ p, A.lat p Γ' = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨g', hg'St, he⟩ := mem_rat hg p
    obtain ⟨-, hsub⟩ := hgp p g' he
    have hSD := (TermBasic.term_basic _ _ _ _ _ _ (hT.2 p)).1
    have hmem : (n p)⁻¹ * g' ∈ (G.S p).St := (G.S p).St.mul_mem ((G.S p).St.inv_mem (hn p).1) hg'St
    have hu : (n p)⁻¹ * g' ∈ isomG (A.L p) (G.S p).Hm :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hmem).1).1).1
    have hle : ∀ x ∈ A.lat p Γ, ((n p)⁻¹ * g') x ∈ A.lat p Γ := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hsub x hx
      have h2 : ((n p)⁻¹ * g') x = x + y := by
        have h3 : (n p).symm (g' x) = ((n p)⁻¹ * g') x := rfl
        rw [← h3, ← sub_eq_iff_eq_add', hxy]
        simp
      rw [h2]
      exact add_mem hx hy
    have hst := smul_eq_of_le (A.L p) _ _ hSD _ hu hle
    rw [(RatExt.rational_extend A _ p).2.2.2.1 g g' Γ he, (hn p).2]
    rw [show g' • A.lat p Γ = n p • (((n p)⁻¹ * g') • A.lat p Γ) by
      rw [← mul_smul, mul_inv_cancel_left], hst]
  refine ⟨g, hg, le_antisymm ?_ ?_⟩
  · intro x hx
    refine (recΓ'.1 x).2 fun p => ?_
    rw [hloc p]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · intro x hx
    have hx' := (recΓ'.1 x).1 hx
    refine ⟨g.symm x, (recΓ.1 _).2 fun p => ?_, by simp⟩
    obtain ⟨g', -, he⟩ := mem_rat hg p
    have h1 := hx' p
    rw [hloc p, (RatExt.rational_extend A _ p).2.2.2.1 g g' Γ he] at h1
    have h2 : A.bc p x = g' • A.bc p (g.symm x) := by
      change _ = g' (A.bc p (g.symm x))
      rw [he, LinearEquiv.apply_symm_apply]
    rw [h2] at h1
    obtain ⟨y, hy, hy'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    rw [smul_left_cancel_iff] at hy'
    exact hy' ▸ hy

end GlobalTheory.HL.GlobalOrbits

namespace GlobalTheory.HL.GlobalOrbits

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem glue_terms (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat} {Λ₀ : G.Lt}
    (h₀ : G.IsTerm d Λ₀) (Λ : ∀ p, Submodule (A.L p).O (G.S p).V)
    (hΛ : ∀ p, (G.S p).IsTerm (d p) (Λ p)) :
    ∃ Γ, G.IsTerm d Γ ∧ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ = h • Λ p := by
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  have rec₀ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Λ₀ h₀.1
  obtain ⟨B, hBfin, hB⟩ : ∃ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite ∧ ∀ p ∉ B,
      A.lat p Λ₀ = Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)) ∧
      ∃ h ∈ (G.S p).St, Λ p = h • Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)) := by
    refine ⟨_, hstd.union rec₀.2.2, fun p hp => ?_⟩
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    obtain ⟨⟨-, -, -, d₀, hW, -, -, hT1, -, -⟩, hl⟩ := hp
    have hTp : (G.S p).IsTerm (d p) (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) := by
      rw [← hl]; exact h₀.2 p
    have hd : d₀ = d p :=
      (TermBasic.term_basic _ _ _ _ _ _ hTp).2.2.2.2.2.2.2 d₀ ⟨(1, 1), hW⟩
    refine ⟨hl, hT1 (Λ p) ?_⟩
    rw [hd]; exact hΛ p
  let Λ' : ∀ p, Submodule (A.L p).O (G.S p).V := fun p => if p ∈ B then Λ p else
    Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))
  have hterm : ∀ p, (G.S p).IsTerm (d p) (Λ' p) := by
    intro p
    by_cases hp : p ∈ B
    · simp only [Λ', if_pos hp]; exact hΛ p
    · simp only [Λ', if_neg hp]; rw [← (hB p hp).1]; exact h₀.2 p
  have hlat : ∀ p, IsLat (A.L p) (Λ' p) := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    exact (TermBasic.term_basic _ _ _ _ _ _ (hterm p)).1.1
  have hfin : {p | Λ' p ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep))}.Finite := by
    refine hBfin.subset fun p hp => ?_
    by_contra hc
    apply hp
    simp only [Λ', if_neg hc]
  obtain ⟨Γ, ⟨hL, hlatΓ⟩, -⟩ := GlobalTheory.T.exists_unique_global_lattice_of_local_lattices A _ Λ' hlat hfin
  refine ⟨Γ, ⟨hL, fun p => (hlatΓ p).symm ▸ hterm p⟩, fun p => ?_⟩
  by_cases hp : p ∈ B
  · refine ⟨1, (G.S p).St.one_mem, ?_⟩
    rw [hlatΓ p, one_smul]
    simp only [Λ', if_pos hp]
  · obtain ⟨h, hh, he⟩ := (hB p hp).2
    refine ⟨h⁻¹, (G.S p).St.inv_mem hh, ?_⟩
    rw [hlatΓ p, he, inv_smul_smul]
    simp only [Λ', if_neg hp]

end GlobalTheory.HL.GlobalOrbits

open GlobalTheory.HL.GlobalOrbits in

theorem GlobalTheory.HL.GlobalOrbits.global_terms_orbits : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → (∀ Λ : ∀ p, Submodule (A.L p).O (G.S p).V, (∀ p, (G.S p).IsTerm (d p) (Λ p)) → ∃ Γ, G.IsTerm d Γ ∧ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ = h • Λ p) ∧ (∀ Γ Γ', G.IsTerm d Γ → Submodule.IsLattice E Γ' → (G.LRel Γ Γ' ↔ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ' = h • A.lat p Γ)) ∧ Equivalence G.LRel ∧ Equivalence G.DRel := by
  intro F E _ _ _ _ _ sig A r k G hk d hex
  obtain ⟨Λ₀, h₀⟩ := hex
  exact ⟨fun Λ hΛ => glue_terms G hk h₀ Λ hΛ,
    fun Γ Γ' hT hL' => ⟨fun h => local_of_lrel G h, fun H => lrel_of_local G hT hL' H⟩,
    lrel_equivalence G, drel_equivalence G⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalSumsEqConstMulCoordinateSumsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLocalSums_eq_const_mul_coordinateSums : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ LocNG.sumSq R d0 (LocNG.BBne (H := H)) = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧ LocNG.sumSq R d0 (fun t => ¬ LocNG.BBne (H := H) t) = ENNReal.ofReal κ * S.ampSq S.BBzero ∧ LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧ LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  first | exact @GlobalTheory.HL.CoordSq.sums_eq | exact GlobalTheory.HL.CoordSq.sums_eq | (intros; apply GlobalTheory.HL.CoordSq.sums_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapCompNegStatement
section
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) → ∀ v : V, GlobalTheory.RowStab.gen H J e ρ c (GlobalTheory.RowStab.gen H J e (-ρ) c' v) = v := by
  first | exact @GlobalTheory.RowStab.gen_comp_gen_neg | exact GlobalTheory.RowStab.gen_comp_gen_neg | (intros; apply GlobalTheory.RowStab.gen_comp_gen_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapIsometryStatement
section
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) → ∀ u v : V, H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  first | exact @GlobalTheory.RowStab.gen_isometry | exact GlobalTheory.RowStab.gen_isometry | (intros; apply GlobalTheory.RowStab.gen_isometry <;> assumption)
end

