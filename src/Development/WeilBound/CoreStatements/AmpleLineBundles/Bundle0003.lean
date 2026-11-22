import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsSecOfFlatPull
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.WeilBound.CoreStatements.AmpleLineBundles.FrameBasis
import Development.WeilBound.CoreStatements.AmpleLineBundles.RhoEventually
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111

-- bundled from Development.WeilBound.CoreStatements.AmpleLineBundles.IsPrincipalIffOfBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace CoverDenseAlt

theorem isAmpleLB_desc {K K' : Type} [Field K] [Field K'] (e : K →+* K') {X X' : Scheme.{0}} (p : X ⟶ Sp K)
    (p' : X' ⟶ Sp K') (φ : X' ⟶ X) (H : IsPullback φ p' p (spMap e)) [IsProper p] (L : LB X) (hL : L.IsLB)
    (h : GlobalTheory.IsAmpleLB (L.pull φ)) : GlobalTheory.IsAmpleLB L := by
  letI := e.toAlgebra
  have hp' : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have hc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hs : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hfl : Flat (spMap e) := inferInstance
  have hsu : Surjective (spMap e) := inferInstance
  have hφ : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) H.flip hsu
  refine ⟨hL, hc, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := φ.surjective x
  obtain ⟨n, hn, s', hs', -⟩ := h.exists_affine y
  have hM := GlobalTheory.isLB_lbPow hL n
  have hM' := GlobalTheory.isLB_lbPow h.isLB n
  have hP := LB.isLB_pull hM φ
  have iso := GlobalTheory.lbIso_lbPow_pull hL φ n
  obtain ⟨s₁, e₁⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hP hM' iso.symm s'
  obtain ⟨σ, hσ⟩ := exists_sec_of_flat_pull p p' φ H (fun U W hU hW => hU.inf hW) _ hM s₁ y (e₁.ge hs')
  refine ⟨n, hn, σ, hσ, ?_⟩
  obtain ⟨s₂, e₂⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hM' hP iso (GlobalTheory.secPull σ φ)
  have ha := h.isAffineOpen_nonzeroLocus p' hn s₂
  rw [e₂, GlobalTheory.nonzeroLocus_secPull] at ha
  have : IsAffine (φ ⁻¹ᵁ Out.nonzeroLocus σ) := ha
  exact GlobalTheory.isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict φ (Out.nonzeroLocus σ)).paste_vert H)

theorem kTriv_desc {S S' : Scheme.{0}} {f : S' ⟶ S} [Flat f] [Surjective f] {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : Out.KTriv A' L') : Out.KTriv A L := by
  intro R _ t x hx
  let T' : Over S' := Over.mk (pullback.snd t f)
  let u : Over.mk (T'.hom ≫ f) ⟶ Over.mk t := Over.homMk (pullback.fst t f) pullback.condition
  have sq : (pullback.fst t f ≫ x.left) ≫ A.hom = pullback.snd t f ≫ f := by
    rw [Category.assoc, Over.w x]; exact pullback.condition
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have e : pushPt h.1.w x' = u ≫ x := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  have m : GlobalTheory.MemKL A' L' x' := GlobalTheory.memKL_of_push h hL hL' hw x' (by rw [e]; exact GlobalTheory.MemKL.comp (A := A) (L := L) (x := x) hx u)
  obtain ⟨z, hz⟩ := (GlobalTheory.memKL_iff_of_kTriv hL' hK x').1 m
  have hx' : x' = 1 := by rw [← hz, toUnit_unique z (toUnit _)]; rfl
  have e₁ : u ≫ x = u ≫ (toUnit _ ≫ η[A]) := by
    rw [← e, hx', ← Category.assoc, comp_toUnit]
    exact map_one (pushHom h T')
  have : Epi (pullback.fst t f) := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi (pullback.fst t f)).1 (congrArg (fun q => q.left) e₁))

theorem isPrincipal_iff_of_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  intro E _ _ _ H L L' _ _ e t t' m
  obtain ⟨w, hw, -⟩ := m.lin
  have hfl : Flat (spMap e) := inferInstance
  have hsu : Surjective (spMap e) := inferInstance
  constructor
  · rintro ⟨hp, ha, hk⟩
    have := t.semi.smooth
    have := t.semi.separated
    have : UniversallyClosed t.G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) m.cart.1.flip ⟨⟨hsu, hfl⟩, inferInstance⟩ inferInstance
    have hp₀ : IsProper t.G.hom := {}
    refine ⟨hp₀, ?_, kTriv_desc m.cart t.PP.isLB t'.PP.isLB ⟨w, hw⟩ hk⟩
    refine (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine t.G t.PP.isLB).2
      (isAmpleLB_desc e t.G.hom t'.G.hom m.φ m.cart.1 _ t.PP.isLB ?_)
    exact (GlobalTheory.isAmpleLB_of_relAmple_of_isAffine t'.G t'.PP.isLB ha).of_lbIso (LB.isLB_pull t.PP.isLB _)
      (LBIso.symm ⟨w, hw⟩)
  · rintro ⟨hp, ha, hk⟩
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp,
      amplePt _ _ _ _ _ _ m.cart _ _ t.PP.isLB t'.PP.isLB ⟨w, hw⟩ ha hk⟩

end CoverDenseAlt
end

-- bundled from Development.WeilBound.CoreStatements.AmpleLineBundles.NonemptyLieMetricOfCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CoverDenseAlt

open Met GlobalTheory.CompanionTheory.Ar.RootHt

theorem nonempty_lie_metric_of_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), Nonempty (LieMetric M y) := by
  classical
  intro X Ω _ K _ J _ y ξ _ hall tie G _ _ _ Li _ _ M
  have hξ := tie.gen
  have key := GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y tie ℂ
  choose n P B hB hcov using fun c => chart_cover tie (lieLat_isVB_of_smooth X Ω ξ G Li M hξ inferInstance).1 c
  choose wz hwz using fun z : Sp ℂ ⟶ X => key.2.1 z (hall _)
  let Λ := Σ c : (k : K) → J k, Fin (n c)
  let f : Λ → ((Σ k, J k) → ℂ) → ℝ := fun l => wt l.1 (P l.1 l.2)
  have hf : ∀ w l, 0 ≤ f l w := fun w l => wt_nonneg _ _ _
  have hne : ∀ {z : Sp ℂ ⟶ X} {w}, CoordsAt ξ y z w → ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 :=
    fun h k => (h.1 k).imp fun _ hi => hi.ne_zero
  have frame : ∀ {z : Sp ℂ ⟶ X} {w}, CoordsAt ξ y z w → ∀ l, f l w ≠ 0 →
      M.lat.IsFrameAt (B l.1 l.2) ⟨centre z, hall _⟩ := by
    intro z w h l hl
    obtain ⟨h1, h2⟩ := wt_ne hl
    exact hB _ _ _ (ArchB.in_chart (hall _) h h1) ((unitAt_iff hξ _ (val_evp (hall _) h l.1 h1 _)).2 h2)
  have pos : ∀ {z : Sp ℂ ⟶ X} {w}, CoordsAt ξ y z w → ∃ l, 0 < f l w := by
    intro z w h
    obtain ⟨c, hc, hc'⟩ := exists_chi (hne h)
    obtain ⟨l, hl⟩ := hcov c _ (ArchB.in_chart (hall _) h hc)
    refine ⟨⟨c, l⟩, mul_pos (lt_max_of_lt_right (by rw [hc']; norm_num)) (norm_pos_iff.2 ?_)⟩
    exact (unitAt_iff hξ _ (val_evp (hall _) h c hc _)).1 hl
  have indep : ∀ {z : Sp ℂ ⟶ X} {w}, CoordsAt ξ y z w → ∀ l, rho f l (wz z) = rho f l w := by
    intro z w h l
    obtain ⟨a, ha⟩ := ((key.2.2 z w (hall _) h).2 _).1 (hwz z)
    have : ∀ m, f m (wz z) = f m w := fun m => by
      simp only [f, wt]
      rw [ha, chi_smul _ w (fun k => (a k : ℂ)) fun k => (a k).ne_zero,
        evp_smul _ _ w (fun k => (a k : ℂ)) fun k => (a k).ne_zero]
    simp only [rho, this]
  have hcj : ∀ (z : Sp ℂ ⟶ X) l, rho f l (wz (spMap (starRingEnd ℂ) ≫ z)) = rho f l (wz z) := by
    intro z l
    rw [indep (PullCoords.coordsAt_field (starRingEnd ℂ) (hwz z))]
    have : ∀ m, f m (fun p => starRingEnd ℂ (wz z p)) = f m (wz z) := fun m => by
      simp only [f, wt]
      rw [chi_conj, evp_conj, RCLike.norm_conj]
    simp only [rho, this]
  refine ⟨{ ip := fun z v v' => ∑ l : Λ, (rho f l (wz z) : ℂ) *
              ∑ i, starRingEnd ℂ (co M (B l.1 l.2) z v i) * co M (B l.1 l.2) z v' i
            herm := fun z V _ _ Mz => ?_
            conj := fun z v w v' w' hv hw => ?_
            cont := fun a b => ?_ }⟩
  · have h : ∀ l : Λ, ∃ g : V →ₗ[ℂ] (Fin (Module.finrank Ω Li) → ℂ), rho f l (wz z) ≠ 0 →
        Function.Injective g ∧ ∀ u, co M (B l.1 l.2) z (Mz.pt u) = g u := by
      intro l
      by_cases hl : rho f l (wz z) = 0
      · exact ⟨0, fun h => (h hl).elim⟩
      obtain ⟨β, hβ, -⟩ := frame_basis hξ M _ z _ (frame (hwz z) l (rho_ne f (hf _) hl)) Mz
      exact ⟨β.equivFun.toLinearMap, fun _ => ⟨β.equivFun.injective, fun u => co_eq M _ z Mz β hβ u⟩⟩
    choose g hg using h
    obtain ⟨l₀, h₀⟩ := exists_rho_pos f (pos (hwz z))
    obtain ⟨core, hcore⟩ := exists_core (fun l => rho f l (wz z)) (fun l => rho_nonneg f l _) g l₀ h₀ (hg l₀ h₀.ne').1
    refine ⟨core, fun a b => (hcore a b).trans (Finset.sum_congr rfl fun l _ => ?_)⟩
    by_cases hl : rho f l (wz z) = 0
    · simp only [hl, Complex.ofReal_zero, zero_mul]
    · rw [(hg l hl).2, (hg l hl).2]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : rho f l (wz (spMap (starRingEnd ℂ) ≫ z)) = 0
    · rw [← hcj z l]
      simp only [hl, Complex.ofReal_zero, zero_mul, map_zero]
    · have hfr := frame (hwz _) l (rho_ne f (hf _) hl)
      rw [map_mul, Complex.conj_ofReal, hcj, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [co_conj hξ M _ z _ hfr v v' hv, co_conj hξ M _ z _ hfr w w' hw, map_mul]
  · refine ⟨fun w => ∑ l : Λ, (rho f l w : ℂ) *
      ∑ i, starRingEnd ℂ (vl ξ y ((B l.1 l.2).repr a i) w) * vl ξ y ((B l.1 l.2).repr b i) w, ?_, ?_⟩
    · rintro w₀ ⟨z₀, va, vb, h₀, ha, hb⟩
      have hc : ∀ l, ContinuousAt (f l) w₀ := fun l => wt_cont _ _ (hne h₀)
      refine ContinuousWithinAt.mono (t := {w | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w}) ?_
        fun w ⟨z, _, _, h, _⟩ => ⟨z, h⟩
      refine tendsto_finset_sum _ fun l _ => ?_
      by_cases hl : f l w₀ = 0
      · have h1 := rho_eventually f hc (hf _) (pos h₀) hl
        refine (ContinuousAt.continuousWithinAt ((continuousAt_const (y := (0 : ℂ))).congr (h1.mono fun v hv => ?_)))
        simp only [hv, Complex.ofReal_zero, zero_mul]
      · have hfr := frame h₀ l hl
        refine ContinuousWithinAt.mul
          (Complex.continuous_ofReal.continuousAt.comp (rho_cont f hc l)).continuousWithinAt
          (tendsto_finset_sum _ fun i _ => ContinuousWithinAt.mul ?_ ?_)
        · exact Complex.continuous_conj.continuousAt.comp_continuousWithinAt
            (vl_cont hall tie h₀ (co_val hξ M _ z₀ _ hfr ha i))
        · exact vl_cont hall tie h₀ (co_val hξ M _ z₀ _ hfr hb i)
    · intro z w va vb h ha hb
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [indep h]
      by_cases hl : rho f l w = 0
      · simp only [hl, Complex.ofReal_zero, zero_mul]
      · have hfr := frame h l (rho_ne f (hf _) hl)
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [vl_eq hall tie h (co_val hξ M _ z _ hfr ha i), vl_eq hall tie h (co_val hξ M _ z _ hfr hb i)]

end CoverDenseAlt
end
end

