import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapLabelPartPreimageRationalSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.PartSpan

theorem mem_span_rat {K V E : Type} [Field K] [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℂ E]
    {τ : K →+* ℂ} {n : ℕ} (u : (Fin n → K) →ₛₗ[τ] V) (Φ : V →ₗ[ℂ] E) (P : Submodule ℂ E)
    (hinj : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0)
    (hspan : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ P →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ P ∧ u a = y}))
    (x : V) (hx : x ∈ Submodule.span ℂ (Set.range u)) (hP : Φ x ∈ P) :
    x ∈ Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} := by
  have hexp : ∀ a : Fin n → K, u a = ∑ k, τ (a k) • u (Pi.single k 1) := by
    intro a
    have ha : a = ∑ k, a k • (Pi.single k 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    simp only [map_sum, map_smulₛₗ]
  have hsp : ∀ z ∈ Submodule.span ℂ (Set.range u), ∃ c : Fin n → ℂ, z = ∑ k, c k • u (Pi.single k 1) := by
    intro z hz
    have hle : Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range fun k => u (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, hexp]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hz)
    exact ⟨c, hc.symm⟩
  obtain ⟨c, rfl⟩ := hsp x hx
  have h1 := hspan c hP
  rw [← Submodule.map_span] at h1
  obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
  have hsS : Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} ≤ Submodule.span ℂ (Set.range u) :=
    Submodule.span_mono (by rintro _ ⟨a, -, rfl⟩; exact ⟨a, rfl⟩)
  obtain ⟨d, rfl⟩ := hsp w (hsS hw)
  have hcd : c - d = 0 := by
    apply hinj
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, map_sub, hwe, sub_self]
  rw [sub_eq_zero.1 hcd]
  exact hw

set_option maxHeartbeats 4000000 in

theorem mem_span_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), ∀ x ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → x ∈ Submodule.span ℂ {y | ∃ a, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p ∧ D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) = y} := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p x hx hW
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have e1 := GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  have h5 := hR.lifts0.1
  let Φ : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H :=
    (Y.mj.eW i).comp (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1))
  let u := ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap).comp
    (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVecLin
  let m : (R.HW i (sg0 D A3.A)).H →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.toCx3 F).W i := Tw.mkL (twAt D.what₂.embLL A3.A.v0) _
  have hcon : ∀ a, m (Φ (u a)) =
      (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) := by
    intro a
    refine Eq.trans ?_ ((R.toCx3 F).tC_cpt_eq F.cr false i t a).symm
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))))) =
      R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) (F.cr.toL (R.toCx3 F).zs false i t a))
    have h3' : F.cr.toL (R.toCx3 F).zs false i t a =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) :=
      (GlobalTheory.Mem.LiftTheta.levelFormCoordinateMap_levelZero F.lv2 hOk (A3.fam3.toSub2 (zsOf R F)) i t a).symm
    rw [hP.phs i, one_smul, e1, h3']
    rfl

  have hsing : ∀ k : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)),
      cpt A3.fam3.base3.v0.embedding (Pi.single k (1 : D.what₂.LL)) = Pi.single k 1 := by
    intro k
    funext j
    by_cases h : j = k
    · subst h; simp [cpt]
    · simp [cpt, Pi.single_apply, h]
  have hsum : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, m (Φ (∑ k, c k • u (Pi.single k 1))) =
      (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) := by
    intro c
    have hc : (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        ∑ k, cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    refine Eq.trans ?_ (congrArg ((R.toCx3 F).tC F.cr false i t) hc).symm
    rw [map_sum, map_sum]
    refine Eq.trans ?_ (map_sum ((R.toCx3 F).tC F.cr false i t) (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    refine Eq.trans ?_ (map_smul ((R.toCx3 F).tC F.cr false i t) _ _).symm
    exact congrArg (fun z => cj (twAt D.what₂.embLL A3.A.v0) (c k) • z)
      ((hcon (Pi.single k 1)).trans (congrArg ((R.toCx3 F).tC F.cr false i t) (hsing k)))

  have hinj : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0 := by
    intro c hc
    have h0 : (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        0 := by
      rw [← hsum c]
      show Tw.mk _ (Φ _) = 0
      rw [hc]
      rfl
    have h1 := (h5 i t).1 (h0.trans (map_zero _).symm)
    funext k
    have hk := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrFun h1 k)
    rw [Links.cj_cj] at hk
    exact hk.trans (map_zero (cj (twAt D.what₂.embLL A3.A.v0)))
  have hw0 := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
  have hC : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≤
      Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) := by
    have hSpW : Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) ≤
        (R.toCx3 F).Wp i p := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      exact ha
    have hle := finrank_le_cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).w0C false i) hw0
      (Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})))
      ((R.toCx3 F).WpK false i p) (fun y hy => by
        obtain ⟨a, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) h5 hR.ratTh i t).2 y
        have hk := (R.toCx3 F).key_lift F.cr false h5 hR.ratTh i t a
        have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMat F.cr false i t *ᵥ a)) ∈
            (R.toCx3 F).Wp i p := hy
        rw [hk, ← hcon a] at hy'
        rw [hk, ← hcon a]
        exact Submodule.subset_span ⟨Φ (u a), ⟨u a, ⟨a, hy', rfl⟩, rfl⟩, rfl⟩)
    rw [(R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 h5 hR.ratTh hR.liftHyp0.h3W hR.partsW i p] at hle
    have heq := Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hSpW) hle
    exact heq.symm.le.trans inf_le_left
  have hspan : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ R.Wp3 i p →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y}) := by
    intro c hc
    have hm : m (Φ (∑ k, c k • u (Pi.single k 1))) ∈
        (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      refine ⟨hc, ?_⟩
      rw [← (h5 i t).2]
      exact ⟨_, (hsum c).symm⟩
    have h1 := hC hm
    rw [← Submodule.map_span] at h1
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
    have hwe' : w = Φ (∑ k, c k • u (Pi.single k 1)) := hwe
    rw [← hwe']
    exact hw
  exact mem_span_rat u Φ (R.Wp3 i p) hinj hspan x hx hW

end GlobalTheory.Mem.R3.PartSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.KerSpan

variable {K : Type} [Field K] {σ : K →+* ℂ}

theorem semi_expand {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (f : (Fin m → K) →ₛₗ[σ] W) (v : Fin m → K) :
    f v = ∑ l, σ (v l) • f (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← map_smulₛₗ]
  congr 1
  ext k
  by_cases h : k = l
  · subst h; simp
  · simp [h]

theorem left_inv_of_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0) :
    ∃ L : Matrix (Fin d) (Fin m) K, L * Θ = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Θ)
    (LinearMap.ker_eq_bot'.2 fun a ha => hΘ a ha)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h

theorem map_mulVec_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (c : Fin d → ℂ) (hc : (Θ.map σ) *ᵥ c = 0) : c = 0 := by
  obtain ⟨L, hL⟩ := left_inv_of_inj Θ hΘ
  have h1 : (L.map σ) * (Θ.map σ) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  calc c = ((L.map σ) * (Θ.map σ)) *ᵥ c := by rw [h1, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]

theorem orth_ker_eq_span [NumberField K] [StarRing K] {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [AddCommGroup W] [Module ℂ W]
    {n d m : ℕ} (j : (Fin n → K) →ₛₗ[σ] V) (H : Matrix (Fin n) (Fin n) K)
    (hinner : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y))
    (hspan : Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤)
    (Z : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hp : Formalism.DivisionValues.IsOrthProj H Z Pr)
    (θ : V →ₗ[ℂ] W) (jW : (Fin m → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (hθ : ∀ x, θ (j x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ)ᗮ = Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) := by
  set U := Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) with hU
  set r : (Fin n → K) → V := fun x => j (x - Z *ᵥ (Pr *ᵥ x)) with hr
  set R := Submodule.span ℂ (Set.range r) with hR
  have hPZ : ∀ a, Pr *ᵥ (Z *ᵥ a) = a := fun a => by rw [Matrix.mulVec_mulVec, hp.1, Matrix.one_mulVec]
  have hθr : ∀ x, θ (r x) = 0 := fun x => by
    simp only [hr]
    rw [hθ, Matrix.mulVec_sub, hPZ, sub_self, Matrix.mulVec_zero, map_zero]
  have horth : ∀ a x, inner ℂ (j (Z *ᵥ a)) (r x) = 0 := fun a x => by
    simp only [hr]
    rw [hinner, map_sub, GlobalTheory.Mem.LiftForms.hform_orth hp, sub_self, map_zero]
  have hRk : R ≤ LinearMap.ker θ := Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hθr x)
  have hUR : U ≤ Rᗮ := by
    have h : U ⟂ R := Submodule.isOrtho_span.2 (by rintro _ ⟨a, rfl⟩ _ ⟨x, rfl⟩; exact horth a x)
    exact h
  have htop : ∀ y : V, ∃ a ∈ U, ∃ b ∈ R, y = a + b := by
    intro y
    have hle : (⊤ : Submodule ℂ V) ≤ U ⊔ R := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have e : j (Pi.single k 1) = j (Z *ᵥ (Pr *ᵥ Pi.single k 1)) + r (Pi.single k 1) := by
        simp only [hr]; rw [map_sub, add_sub_cancel]
      rw [SetLike.mem_coe]
      dsimp only
      rw [e]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle Submodule.mem_top)
    exact ⟨a, ha, b, hb, e.symm⟩
  have hinj : ∀ y ∈ U, θ y = 0 → y = 0 := by
    intro y hy h0
    have hsub : U ≤ Submodule.span ℂ (Set.range fun k => j (Z *ᵥ Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe]
      dsimp only
      rw [show j (Z *ᵥ a) = (j.comp (Matrix.mulVecLin Z)) a from rfl, semi_expand]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsub hy)
    have hc : (Θ.map σ) *ᵥ c = 0 := by
      rw [map_sum] at h0
      simp only [map_smul, hθ, hPZ] at h0
      have e : ∀ k, jW (Θ *ᵥ Pi.single k 1) = ∑ l, σ (Θ l k) • jW (Pi.single l 1) := fun k => by
        rw [semi_expand jW]
        simp
      have h1 : ∑ k, c k • jW (Θ *ᵥ Pi.single k 1) = ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by
        simp only [e, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1] at h0
      exact funext (Fintype.linearIndependent_iff.1 hli _ h0)
    have hc0 := map_mulVec_inj Θ hΘ c hc
    subst hc0
    simp
  have hker : LinearMap.ker θ = R := by
    refine le_antisymm (fun y hy => ?_) hRk
    obtain ⟨a, ha, b, hb, rfl⟩ := htop y
    have hb0 : θ b = 0 := hRk hb
    have ha0 : θ a = 0 := by
      rw [LinearMap.mem_ker, map_add, hb0, add_zero] at hy; exact hy
    rw [hinj a ha ha0, zero_add]; exact hb
  rw [hker]
  refine le_antisymm (fun y hy => ?_) hUR
  obtain ⟨a, ha, b, hb, rfl⟩ := htop y
  have hb' : b ∈ Rᗮ := by
    have h := Rᗮ.sub_mem hy (hUR ha); rwa [add_sub_cancel_left] at h
  have hb0 : b = 0 := by
    have h : b ∈ R ⊓ Rᗮ := Submodule.mem_inf.2 ⟨hb, hb'⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h
    exact (Submodule.mem_bot ℂ).1 h
  rw [hb0, add_zero]; exact ha

set_option maxHeartbeats 2000000 in

theorem orth_ker_thetaP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have hT := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hΘ : ∀ a, ((A3.indefDown (s0Of R F)).θ i t) *ᵥ a = 0 → a = 0 := by
    intro a ha
    have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false hR.lifts0.1 hR.ratTh i t a
    have h6 := CxData.tC_cpt_eq (R.toCx3 F) F.cr false i t a
    have ha' : (R.toCx3 F).liftMat F.cr false i t *ᵥ a = 0 := ha
    have h7 : (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) = (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding 0) := by
      rw [h6, ← h2, ha']
      have hz : ∀ {k : ℕ}, cpt A3.fam3.base3.v0.embedding (0 : Fin k → D.what₂.LL) = 0 := fun {k} => by
        funext l; simp [cpt]
      simp only [hz, map_zero]
    exact cpt_injective _ ((hR.lifts0.1 i t).1 h7)
  exact GlobalTheory.Mem.KerSpan.orth_ker_eq_span _ _ (Y.formsL i t).inner (Y.formsL i t).span _ _ hp
    (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (Z.jW i) (hT.1.li i) _ hΘ (fun x => hT.2 i t x)

end GlobalTheory.Mem.KerSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PenultimateChartLocalGroupMemNearLevelSet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.NearLev

def triv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) :
    StepLevel F E σ J T f bad :=
  { S with chi := 1, chi_triv := fun _ _ => rfl }

theorem chiFin_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {T i : ℕ} {hi : i ≤ B.R.m}
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) :
    ChiFin I l Z (triv S) :=
  ⟨1, one_pos, fun _ _ => by simp only [triv, pow_one]; rfl⟩

set_option maxHeartbeats 4000000 in

theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (κ : (K (chOf c)).lev.U), ∃ x : (K (chOf c)).lev.U, (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = UAd B.sp.cm (B.R.N i) := by rw [hg]; rfl
  set y : GA B (B.R.N i) := ((K (chOf c)).y ⟨c, rfl⟩).1 with hy
  set kk : GA B (B.R.N i) := k (chOf c) with hkk
  have hsel : ∀ P : SBof I a, ∃ z : (K (chOf c)).lev.U,
      (∀ P' : SBof I a, P' ≠ P → ∀ r s, adAt B.host.F P'.1 (((show GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P'.1.adicCompletion B.fields.E)) r s) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) z.1 ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 ((((y * (show GA B (B.R.N i) from κ.1)) * (show GA B (B.R.N i) from z.1) * kk : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, -, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a _ i hi bad (triv (K (chOf c)).lev) (chiFin_triv I l Z _) P hP v hv ((I.cst a).D P) (y * (show GA B (B.R.N i) from κ.1)) kk
      refine ⟨⟨z.1, z.2⟩, fun P' hP' r s => ?_, hz3, fun _ => hz4⟩
      have e := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P' z.1).1
      have h2 := hv' P' hP'
      rw [e] at h2
      exact LevelElt.support_one z.1 v hz2 P'.1 h2 r s
    · refine ⟨1, fun P' _ r s => ?_, GlobalTheory.TwU.congAt_one _ _, fun h => absurd h hP⟩
      show adAt B.host.F P'.1 ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = _
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  choose zf hzf2 hzf3 hzf4 using hsel
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : (K (chOf c)).lev.U →* GA B (B.R.N i) := (K (chOf c)).lev.U.subtype
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := fun P P' h => Matrix.ext fun r s => by
    rw [cP_apply]; exact hzf2 P P' h r s
  have hlist : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : (K (chOf c)).lev.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlist _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hpt : ∀ g : GA B (B.R.N i), g ∈ UAd B.sp.cm (B.R.N i) → (∀ P ∈ I.Q a, ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) → ∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf g q :=
    fun g hg hr => LevelElt.point_of_rat B.sp.cm _ _ _ g hg hr
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨κ * w, ?_, ?_⟩
  · obtain ⟨p0, hp0, -⟩ := hR.k_std (chOf c)
    have hyU : y ∈ UAd B.sp.cm (B.R.N i) := eU ▸ ((K (chOf c)).y ⟨c, rfl⟩).2
    have hxU : (show GA B (B.R.N i) from (κ * w).1) ∈ UAd B.sp.cm (B.R.N i) := eU ▸ (((K (chOf c)).lev.U_eq _).1 (κ * w).2).1
    have hkU : kk ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
    refine hpt _ (mul_mem (mul_mem hyU hxU) hkU) fun P hP => ?_
    let P' : SBof I a := ⟨P, hQsub P hP⟩
    obtain ⟨γ, hγ⟩ := hzf4 P' hP
    refine ⟨γ, fun r s => ?_⟩
    have e1 := LevelElt.mul_comp_eq (cP P) y (show GA B (B.R.N i) from κ.1) (show GA B (B.R.N i) from w.1) (show GA B (B.R.N i) from (zf P').1) kk (hwP P')
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · intro P
    have e : κ.1⁻¹ * (κ * w).1 = w.1 := inv_mul_cancel_left κ.1 w.1
    refine (congrArg (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P)) e).mpr ?_
    refine ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P w.1).2.2).mpr fun r s => ?_
    have e := LevelElt.entry_eq_of_eq (cP P.1) _ _ (hwP P) r s
    have D2 := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P (zf P).1).2.2.1 (hzf3 P)) r s
    convert D2 using 3
    exact e

set_option maxHeartbeats 4000000 in

theorem exists_stepElt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (κ : (K (chOf c)).lev.U), ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ ∀ (P : SBof I a) (f : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((show GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) from k (chOf c))⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F f) → GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F f)⁻¹ * (show GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) from k (chOf c))) → ∀ (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) (fun _ : SBof I a => f) (I.cst a).D P κ.1 g := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  obtain ⟨x, ⟨q, hq⟩, hxκ⟩ := exists_level_elt I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  have hl := hR.lev c x.1 q hq
  have hx : x.1 ∈ (fun β => (K β).lev.U) (chOf c) := x.2
  obtain ⟨κ', h3⟩ := hl.mp hx
  refine ⟨κ', ⟨h3.1, h3.2.2⟩, fun P f he hei g hL => ?_⟩
  obtain ⟨hm1, hm2, hn⟩ := GlobalTheory.T.levelElement_at_bad_primes_integral_and_near I hOk l Z u a i hi bad Ch chOf K k hR c x.1 κ' h3.1 (h3.2.1 ▸ hq) P
  obtain ⟨p, hp, hpN⟩ := hR.k_std (chOf c)
  exact GlobalTheory.T.adelicMatrixCongruence_move_rational_frame _ _ κ.1 x.1 (k (chOf c)) f _ (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).1)
    (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).2) hm1 hm2 (hxκ P) (hn g hL) he hei

end GlobalTheory.Mem.Col2.QChi.NearLev

namespace GlobalTheory.Mem.Col2.QChi

theorem idx_h_last_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ (j : ℕ), j = B.R.m - 2 + 1 → ∀ (b : (I.idx a).β j) (P : SBof I a), (I.idx a).h j b P = 1 := by
  intro j hj
  subst hj
  exact (hOk.idx_ok a).last_h

set_option maxHeartbeats 4000000 in

theorem mem_nearSet_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), x.1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ _ _ hk _ _ Lb0 _ v hv β x
  obtain ⟨k, hR, hk1⟩ := hk
  have hm : B.R.m - 1 < B.R.m := by omega
  have hm2 : B.R.m - 1 = B.R.m - 2 + 1 := by have := hOk.hm; omega
  obtain ⟨c, rfl⟩ := hR.onto β
  intro P hPv
  let κ : (K (chOf c)).lev.U := GlobalTheory.Mem.Col2.ChartLevel.embU (K (chOf c)).lev v x
  obtain ⟨κ', -, hκ'⟩ := NearLev.exists_stepElt I hOk hPins l Z u a (B.R.m - 1) (Nat.sub_le _ _) (badQ (I.rec7 l Z) Q) Ch chOf K k hR c κ
  obtain ⟨g', z, hMid, hL⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a (B.R.m - 1) hm c.1 κ' P
  let kk : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) := k (chOf c)
  have hv1 : bc (prV (E := (I.rec7 l Z).host.E) v) kk = 1 := hk1 (chOf c) v ((hQ v).1 hv)
  have he : GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (kk⁻¹ * 1) :=
    GlobalTheory.AwayFr.congAt_of_prV_eq v _ hPv ((I.cst a).D P) kk 1 ((map_one _).trans hv1.symm)
  have hei : GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (1⁻¹ * kk) :=
    GlobalTheory.AwayFr.congAt_of_prV_eq v _ hPv ((I.cst a).D P) 1 kk (hv1.trans (map_one _).symm)
  have hIF := hκ' P 1 (by rw [map_one]; exact he) (by rw [map_one]; exact hei) g' hL
  refine ⟨g', z, ?_, ?_⟩
  · have h := hMid
    unfold MidAt at h
    rw [idx_h_last_step I hOk a _ hm2] at h
    exact h
  · unfold GlobalTheory.TwU.InFrame at hIF
    rw [map_one, inv_one, one_mul, mul_one] at hIF
    exact hIF

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_form_of_local_inputs : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → GlobalTheory.NRows.Rows D → SumRepresentations.ReducedMultiplicityStatement D := by
  first | exact @GlobalTheory.PtSt.reducedMultiplicity_of_rows | exact GlobalTheory.PtSt.reducedMultiplicity_of_rows | (intros; apply GlobalTheory.PtSt.reducedMultiplicity_of_rows <;> assumption)
end

