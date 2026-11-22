import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerNear
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.PerCoordU GlobalTheory.PeriodCoord

namespace UpperTheory.Gal.W2

theorem perNear_of : PerNear := by
  intro O _ bar g ρ D P₀ M₀ hP hM d co hco
  obtain ⟨hHerm, hPos, hIm⟩ := hM
  have hdet : M₀.det ≠ 0 := det_ne_zero_of_pos hPos
  obtain ⟨t, ht, htO, ht0⟩ := eventually_nhds_iff.mp (T.eventually_posDef_hermForm_near_zero_matrix M₀ hPos)
  have hcont : Continuous co := LinearMap.continuous_of_finiteDimensional co
  refine ⟨co ⁻¹' t, htO.preimage hcont, by simpa using ht0, ?_, ?_⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := ht (co b) hb
    have hT : (co b)ᵀ * M₀ ∈ Tsp bar ρ := hco b
    obtain ⟨hH, hF⟩ := T.riemann_relation_converse_conjAffine M₀ (co b) hHerm hdet hT.1 h1
    have hcomm := comm_of_mem_Tsp hP hIm hdet hT
    refine T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (co b)) (M₀ * (1 - (co b).map star * co b)⁻¹) hP
      (realMap_one_injective h2) ?_ hH h3 ?_
    · intro a x
      simp only [realMap_apply, Matrix.one_mulVec, Matrix.mulVec_add, star_mulVec_map,
        Matrix.mulVec_mulVec, hcomm a]
      rw [Matrix.one_mul]
    · intro x y
      simp only [realMap_apply, Matrix.one_mulVec]
      rw [hF, hIm]
  · intro x
    set v := star (P₀ x)
    let f : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => co b *ᵥ v
        map_add' := by intro a b; simp [Matrix.add_mulVec]
        map_smul' := by intro c b; simp [Matrix.smul_mulVec] }
    have hf : Differentiable ℂ (fun b => co b *ᵥ v) :=
      (LinearMap.toContinuousLinearMap f).differentiable
    have : (fun b => (perC P₀ (co b)) x) = fun b => P₀ x + co b *ᵥ v := by
      funext b; simp [perC_apply, v]
    rw [this]
    exact ((differentiable_const _).add hf).differentiableOn

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_map_ext {X : Scheme.{0}} {A : Over X} {k : ℕ} {T : Scheme.{0}}
    (a b : T ⟶ (GlobalTheory.KS.pow A k).left) (h0 : a ≫ (GlobalTheory.KS.pow A k).hom = b ≫ (GlobalTheory.KS.pow A k).hom)
    (h : ∀ j, a ≫ (GlobalTheory.KS.pr A j).left = b ≫ (GlobalTheory.KS.pr A j).left) : a = b := by
  let Y : Over X := Over.mk (a ≫ (GlobalTheory.KS.pow A k).hom)
  let fa : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk a rfl
  let fb : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk b h0.symm
  have hab : fa = fb := by
    unfold GlobalTheory.KS.pow at fa fb ⊢
    apply Limits.Pi.hom_ext
    intro j
    ext
    simp only [Over.comp_left, Over.homMk_left, fa, fb]
    exact h j
  exact congrArg (fun f => f.left) hab

section
variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D : PLat O bar}
  {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {A : Over X} [GrpObj A] (S : Sheet s A D ρ) (k : ℕ)

private theorem pt_hom (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) :
    S.pt k P z ≫ (GlobalTheory.KS.pow A k).hom = S.u P :=
  Over.w (Pi.lift (fun j => S.ex P (z j)) : Over.mk (S.u P) ⟶ GlobalTheory.KS.pow A k)

private theorem pt_pr (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) (j : Fin k) :
    S.pt k P z ≫ (GlobalTheory.KS.pr A j).left = (S.ex P (z j)).left := by
  unfold Sheet.pt GlobalTheory.KS.pr
  rw [← Over.comp_left, Limits.Pi.lift_π]

private theorem ex_sub (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ρ P) (a b : Fin g → ℂ) :
    S.ex P a = S.ex P (a - b) * S.ex P b := by
  have h := S.exp P hP
  unfold IsExp at h
  have e := h.1 (a - b) b
  rwa [sub_add_cancel] at e

end

theorem UpperTheory.Gal.W2.ptFibre_of :
    UpperTheory.Gal.W2.PtFibre := by
  intro O _ bar g ρ D X s A _ S k P hP
  have hE := S.exp P hP
  unfold IsExp at hE
  have hu : ∀ (P' : D.La →+ (Fin g → ℂ)) (w : Fin g → ℂ), (S.ex P' w).left ≫ A.hom = S.u P' :=
    fun P' w => Over.w (S.ex P' w)
  refine ⟨fun z => pt_hom S k P z, fun z j => pt_pr S k P z j, ?_, ?_, ?_⟩
  · intro y hy
    have hc : ∀ j : Fin k, ∃ w, S.ex P w =
        Over.homMk (U := Over.mk (S.u P)) (V := A) (y ≫ (GlobalTheory.KS.pr A j).left) (by
          show _ = S.u P
          rw [Category.assoc, Over.w]
          exact hy) := fun j => hE.2.1 _
    choose z hz using hc
    refine ⟨z, pow_map_ext _ _ ?_ ?_⟩
    · rw [hy, pt_hom]
    · intro j
      rw [pt_pr, hz j]
      rfl
  · intro z z'
    constructor
    · intro heq j
      have e1 : (S.ex P (z j)).left = (S.ex P (z' j)).left := by
        rw [← pt_pr S k P z j, ← pt_pr S k P z' j, heq]
      have e2 : S.ex P (z j) = S.ex P (z' j) := Over.OverMorphism.ext e1
      have e3 : S.ex P (z j - z' j) = 1 := by
        have e4 := ex_sub S P hP (z j) (z' j)
        rw [e2] at e4
        exact mul_eq_right.mp e4.symm
      exact (S.ker P hP _).mp e3
    · intro hr
      apply pow_map_ext
      · rw [pt_hom, pt_hom]
      · intro j
        rw [pt_pr, pt_pr, ex_sub S P hP (z j) (z' j), (S.ker P hP _).mpr (hr j), _root_.one_mul]
  · intro P' h hP' hx z
    have hu' : S.u P' = S.u P := by
      calc S.u P' = (S.ex P' (h 0)).left ≫ A.hom := (hu P' (h 0)).symm
        _ = (S.ex P 0).left ≫ A.hom := by rw [S.lin P P' h hP hP' hx 0]
        _ = S.u P := hu P 0
    apply pow_map_ext
    · rw [pt_hom, pt_hom, hu']
    · intro j
      rw [pt_pr, pt_pr]
      exact S.lin P P' h hP hP' hx (z j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtHol
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.ptHol_of :
    UpperTheory.Gal.W2.HolPi → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PtHol := by
  intro hHP hPF O _ bar g ρ D X s A _ S k m B P hB hP
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hS := S.hol m B P hB hP
  refine hHP ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X A k (B ×ˢ Set.univ)
    (fun bz => S.pt k (P bz.1) bz.2) hBU ?_ ?_
  · have hu : IsHolTo (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) (fun bz => S.u (P bz.1)) :=
      GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.1 hBU differentiableOn_fst
        (fun bz hbz => hbz.1)
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr hu ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
  · intro j
    let φ : (Fin m → ℂ) × (Fin k → Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) :=
      fun bz => (bz.1, bz.2 j)
    have hφ : Differentiable ℂ φ := by
      fun_prop
    have hmaps : Set.MapsTo φ (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)))
        (B ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      fun bz hbz => ⟨hbz.1, Set.mem_univ _⟩
    have he := GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.2 hBU hφ.differentiableOn hmaps
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr he ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtImm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem flat_of_eventuallyEq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}}
    {s s' : V → (Sp ℂ ⟶ Y)} {v₀ w : V} (h : s =ᶠ[𝓝 v₀] s') (hf : Flat s v₀ w) : Flat s' v₀ w := by
  intro U f hU
  have h0 : s v₀ = s' v₀ := h.eq_of_nhds
  have hfd : fderiv ℂ (fun v => valAt' (s' v) U f) v₀ = fderiv ℂ (fun v => valAt' (s v) U f) v₀ := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h] with v hv
    rw [hv]
  rw [hfd]
  exact hf U f (h0 ▸ hU)

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.W2.ptImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.ExpImm → UpperTheory.Gal.W2.PtImm := by
  intro hComp hPre hPF hExp O _ bar g ρ D X s A _ S k m B P b₀ hB hb₀ hP hu z₀ w hw
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hmem : (b₀, z₀) ∈ B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) := ⟨hb₀, Set.mem_univ _⟩
  have hnhds : B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) ∈ 𝓝 (b₀, z₀) := hBU.mem_nhds hmem
  have hS := S.hol m B P hB hP
  have hw1 : w.1 = 0 := by
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left X (KS.pow A k).hom
      (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => S.u (P bz.1)) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
    have hfst : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => bz.1)
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)) (b₀, z₀) := hasFDerivAt_fst
    have h3 : Flat (fun b => S.u (P b)) b₀
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ) w) :=
      (hPre (Fin m → ℂ) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X B (fun b => S.u (P b)) hS.1
        (fun bz => bz.1) (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ))
        (b₀, z₀) w hfst hb₀).mp h2
    exact hu _ h3
  have hw2 : ∀ j, w.2 j = 0 := by
    intro j
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left A.left
      (Over.Hom.left (KS.pr A j)) (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) =>
        Over.Hom.left (S.ex (P bz.1) (bz.2 j))) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
    let L : (Fin m → ℂ) × (Fin k → Fin g → ℂ) →L[ℂ] (Fin m → ℂ) × (Fin g → ℂ) :=
      (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)).prod
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => Fin g → ℂ) j).comp
          (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)))
    have hL : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => (bz.1, bz.2 j)) L (b₀, z₀) :=
      L.hasFDerivAt
    have hmem2 : ((b₀, z₀).1, (b₀, z₀).2 j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h3 : Flat (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => Over.Hom.left (S.ex (P bz.1) bz.2))
        (b₀, z₀ j) (L w) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun bz => (bz.1, bz.2 j)) L (b₀, z₀) w hL hmem2).mp h2
    have hLw : L w = (0, w.2 j) := by
      simp [L, hw1]
    rw [hLw] at h3
    have hι : HasFDerivAt (fun z : Fin g → ℂ => (b₀, z))
        (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)) (z₀ j) :=
      (hasFDerivAt_const b₀ (z₀ j)).prodMk (hasFDerivAt_id (z₀ j))
    have hmem3 : (fun z : Fin g → ℂ => (b₀, z)) (z₀ j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h4 : Flat (fun z : Fin g → ℂ => Over.Hom.left (S.ex (P b₀) z)) (z₀ j) (w.2 j) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) (Fin g → ℂ) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun z => (b₀, z)) (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ))
        (z₀ j) (w.2 j) hι hmem3).mpr h3
    exact hExp X A g (S.u (P b₀)) (S.ex (P b₀)) (S.exp _ (hP.1 _ hb₀)) (z₀ j) (w.2 j) h4
  exact Prod.ext hw1 (_root_.funext hw2)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanChart_of :
    UpperTheory.Gal.W2.TanDeriv → UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.ConjCharpoly → UpperTheory.Gal.W2.TanChart := by
  intro hTD hFA hCC E _ _ _ d hd Z Y sZ s' c₁ c₂ h₁ h₂ B s v₀ hB hv hs hs' hflat G G' hG hGv hev y hy0 A hT
  obtain ⟨U, W, hW1, hW2, t, hy, hU, hW, φ, hφ1, hφ2, hφ3, hφ4⟩ := hT
  obtain ⟨ψ, hψ1, hψ2⟩ := hTD E Y s' B s v₀ hB hv hs hs' y hy0 W hy
  let e₁ : Fin d → Sec s' W := fun l => Sec.res s' hW1 (appSec sZ s' c₁ U (t l))
  let e₂ : Fin d → Sec s' W := fun l => Sec.res s' hW2 (appSec sZ s' c₂ U (t l))
  have hφ2' : ∀ l, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) = Pi.single l 1 := hφ2
  have hφ3' : ∀ j, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) = fun l => A j l := hφ3
  let N : Set E := {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}
  have hNo : IsOpen N := (hs W 0).1
  have hv₀N : v₀ ∈ N := by
    refine ⟨hv, ?_⟩
    have := hy
    simp only [CxPts.ptsIn, Set.mem_setOf_eq] at this
    rw [hy0] at this
    exact this
  have hNn : N ∈ 𝓝 v₀ := hNo.mem_nhds hv₀N
  have hK : ∀ ω, ψ ω = ∑ l, (φ ω) l • ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) := by
    intro ω
    set ω' := ω - ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) with hω'
    have hφω' : φ ω' = 0 := by
      rw [hω', map_sub, map_sum]
      simp only [map_smul, hφ2']
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    obtain ⟨m, b, ω'', hb0, hωeq⟩ := hφ4 ω' hφω'
    have hψω' : ψ ω' = 0 := by
      rw [hωeq, map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hψ1, hb0 i, zero_smul]
    have hω : ω = ω' + ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) := by
      rw [hω']
      abel
    conv_lhs => rw [hω]
    rw [map_add, hψω', zero_add, map_sum]
    simp only [map_smul]
  let τ : E →ₗ[ℂ] Fin d → ℂ :=
    LinearMap.pi (fun l => ((ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ))
  have hτ : ∀ w l, τ w l = ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) w := fun w l => rfl
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hflat
    refine hFA E Y B s v₀ w hB hv hs W hW hv₀N.2 (fun f => ?_)
    have hf : fderiv ℂ (fun v => valAt' (s v) W f) v₀ = ψ (KaehlerDifferential.D ℂ (Sec s' W) f) :=
      (hψ2 f).symm
    rw [hf, hK, ContinuousLinearMap.sum_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [ContinuousLinearMap.smul_apply, ← hτ, hw]
    simp
  have hval : ∀ (c : Y ⟶ Z) (hc : W ≤ c ⁻¹ᵁ U) (f : Sec sZ U) (v : E), ⊤ ≤ s v ⁻¹ᵁ W →
      valAt' (s v) W (Sec.res s' hc (appSec sZ s' c U f)) = valAt' (s v ≫ c) U f := by
    intro c hc f v hvW
    exact (valAt'_res (s v) hc _ hvW).trans (valAt'_comp (s v) c U f)
  have hrel : ∀ w, τ (G' w) = A *ᵥ τ w := by
    intro w
    funext j
    have hd1 : DifferentiableAt ℂ (fun v => valAt' (s v) W (e₁ j)) v₀ :=
      ((hs W (e₁ j)).2).differentiableAt hNn
    have hGN : ∀ᶠ v in 𝓝 v₀, G v ∈ N := by
      have hNn' : N ∈ 𝓝 (G v₀) := by rw [hGv]; exact hNn
      exact hG.continuousAt.preimage_mem_nhds hNn'
    have heq : (fun v => valAt' (s v) W (e₂ j)) =ᶠ[𝓝 v₀]
        (fun v => valAt' (s v) W (e₁ j)) ∘ G := by
      filter_upwards [hNn, hGN, hev] with v hvN hGvN hevv
      simp only [Function.comp_apply]
      rw [hval c₂ hW2 (t j) v hvN.2, hval c₁ hW1 (t j) (G v) hGvN.2, hevv]
    have hd1' : HasFDerivAt (fun v => valAt' (s v) W (e₁ j))
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀) (G v₀) := by
      rw [hGv]; exact hd1.hasFDerivAt
    have hcomp := hd1'.comp v₀ hG
    have hfd : fderiv ℂ (fun v => valAt' (s v) W (e₂ j)) v₀ =
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀).comp G' := by
      rw [heq.fderiv_eq]
      exact hcomp.fderiv
    have h2 : ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) w = ∑ l, A j l * τ w l := by
      rw [hK, hφ3', ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hτ]
    rw [Matrix.mulVec, dotProduct, ← h2, hψ2, hfd, hτ, hψ2]
    rfl
  exact hCC E d hd τ (G' : E →ₗ[ℂ] E) A hinj hrel
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanDeriv
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem tanDeriv_of : TanDeriv := by
  intro V _ _ Y s' B s v₀ hB hv₀ hs hss y hy W hyW
  have hv₀S : v₀ ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} := ⟨hv₀, by rw [← hy]; exact hyW⟩
  have hnhds : {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} ∈ 𝓝 v₀ := (hs W 0).1.mem_nhds hv₀S
  have hval : ∀ v (hv : v ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}) (b : Sec s' W),
      valAt' (s v) W b = CxPts.ev s' (RingHom.id ℂ) W b ⟨s v, hss v hv.1⟩ := by
    intro v hv b
    simp only [valAt', CxPts.ev, valR, dif_pos hv.2]
    rfl
  let g : Sec s' W → V → ℂ := fun b v => valAt' (s v) W b
  have hd : ∀ b, DifferentiableAt ℂ (g b) v₀ := fun b =>
    ((hs W b).2 v₀ hv₀S).differentiableAt ((hs W b).1.mem_nhds hv₀S)
  have hadd : ∀ b c, g (b + c) =ᶠ[𝓝 v₀] g b + g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b + c) = valAt' (s v) W b + valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_add _ _ _)
  have hmul : ∀ b c, g (b * c) =ᶠ[𝓝 v₀] g b * g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b * c) = valAt' (s v) W b * valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_mul _ _ _)
  have hconst : ∀ a : ℂ, ∀ᶠ v in 𝓝 v₀, g (algebraMap ℂ (Sec s' W) a) v = a := fun a =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (algebraMap ℂ (Sec s' W) a) = a
      rw [hval v hv]
      exact CxPts.ev_algX (show (⟨s v, hss v hv.1⟩ : CxPts s' (RingHom.id ℂ)) ∈ CxPts.ptsIn s' (RingHom.id ℂ) W from hv.2) a)
  have hyeq : (⟨s v₀, hss v₀ hv₀S.1⟩ : CxPts s' (RingHom.id ℂ)) = y := Subtype.ext hy.symm
  have hv0 : ∀ b, g b v₀ = CxPts.evHom hyW b := fun b => by
    change valAt' (s v₀) W b = _
    rw [hval v₀ hv₀S b, hyeq]
    exact CxPts.ev_eq hyW b
  have hφa : ∀ a : ℂ, CxPts.evHom hyW (algebraMap ℂ (Sec s' W) a) = a := fun a =>
    (CxPts.ev_eq hyW _).symm.trans (CxPts.ev_algX hyW a)
  letI : Module (Sec s' W) (V →L[ℂ] ℂ) := Module.compHom _ (CxPts.evHom hyW)
  haveI : IsScalarTower ℂ (Sec s' W) (V →L[ℂ] ℂ) := ⟨fun a b m => by
    change (CxPts.evHom hyW (a • b)) • m = a • ((CxPts.evHom hyW b) • m)
    have h1 : CxPts.evHom hyW (a • b) = a * CxPts.evHom hyW b :=
      (congrArg (CxPts.evHom hyW) (Algebra.smul_def a b)).trans
        ((map_mul (CxPts.evHom hyW) _ _).trans (congrArg (· * CxPts.evHom hyW b) (hφa a)))
    exact (congrArg (· • m) h1).trans (mul_smul _ _ _)⟩
  let L : Sec s' W →ₗ[ℂ] (V →L[ℂ] ℂ) :=
    { toFun := fun b => fderiv ℂ (g b) v₀
      map_add' := fun b c => by
        change fderiv ℂ (g (b + c)) v₀ = fderiv ℂ (g b) v₀ + fderiv ℂ (g c) v₀
        rw [(hadd b c).fderiv_eq, fderiv_add (hd b) (hd c)]
      map_smul' := fun a b => by
        change fderiv ℂ (g (a • b)) v₀ = a • fderiv ℂ (g b) v₀
        have h' : g (a • b) =ᶠ[𝓝 v₀] fun v => a * g b v := by
          rw [Algebra.smul_def]
          filter_upwards [hmul (algebraMap ℂ _ a) b, hconst a] with v h1 h2
          rw [h1, Pi.mul_apply, h2]
        rw [h'.fderiv_eq, fderiv_const_mul (hd b)] }
  let D : Derivation ℂ (Sec s' W) (V →L[ℂ] ℂ) := Derivation.mk' L (fun b c => by
    change fderiv ℂ (g (b * c)) v₀ =
      (CxPts.evHom hyW b) • fderiv ℂ (g c) v₀ + (CxPts.evHom hyW c) • fderiv ℂ (g b) v₀
    rw [(hmul b c).fderiv_eq, fderiv_mul (hd b) (hd c), hv0 b, hv0 c])
  refine ⟨D.liftKaehlerDifferential.restrictScalars ℂ, fun b ω => ?_, fun b => ?_⟩
  · change D.liftKaehlerDifferential (b • ω) = _
    rw [LinearMap.map_smul]
    exact congrArg (· • D.liftKaehlerDifferential ω) (CxPts.ev_eq hyW b).symm
  · change D.liftKaehlerDifferential (KaehlerDifferential.D ℂ _ b) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTriCharpoly
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.triCharpoly_of :
    UpperTheory.Gal.W2.TriCharpoly := by
  intro V W _ _ _ _ _ _ T Θ R G hG
  let bV := Module.finBasis ℂ V
  let bW := Module.finBasis ℂ W
  have hM : LinearMap.toMatrix (bV.prod bW) (bV.prod bW) G =
      Matrix.fromBlocks (LinearMap.toMatrix bV bV T) 0 (LinearMap.toMatrix bV bW R)
        (LinearMap.toMatrix bW bW Θ) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply, hG]
  rw [← LinearMap.charpoly_toMatrix G (bV.prod bW), ← LinearMap.charpoly_toMatrix T bV,
    ← LinearMap.charpoly_toMatrix Θ bW, hM, Matrix.charpoly_fromBlocks_zero₁₂]
end

