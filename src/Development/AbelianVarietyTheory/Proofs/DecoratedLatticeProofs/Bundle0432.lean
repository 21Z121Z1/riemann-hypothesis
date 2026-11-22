import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0377
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0113
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0112
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FrameMoves

variable {D : D7}

theorem mulVec_of_grpOff (S : HSp D) {v : Pl D} {h : GA D S} (hh : h ∈ grpOff S (· = v))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : mt S h *ᵥ y = y := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hy' : ∀ j, GlobalTheory.FinPlLoc.idem D (· = v) * y j = y j := fun j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy j)
  ext i
  calc (mt S h *ᵥ y) i = ∑ j, mt S h i j * y j := rfl
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j) * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [← hy' j]
        ring
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
        simp_rw [hij]
    _ = y i := by
        simp [Matrix.one_apply, hy' i]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_pr_of_grpOff (p : SplitPt D k) (S : HSp D) {h : GA D S} (hh : h ∈ grpOff S (· = p.v)) :
    (mt S h).map p.pr = 1 := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = p.v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = p.v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = p.v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hpr : ∀ x, p.pr x = p.pr (p.e * x) := fun x => by rw [← p.sec_pr, p.pr_sec]
  have he : GlobalTheory.FinPlLoc.idem D (· = p.v) * p.e = p.e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt p)
  rw [← Matrix.map_one p.pr (map_zero _) (map_one _)]
  ext i j
  simp only [Matrix.map_apply]
  rw [hpr, hpr ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j), ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _) p.e,
    mul_assoc, hij i j, ← mul_assoc]

theorem moves_iff_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (A : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (L : GlobalTheory.FinPl.Lat A) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC A L → β.IsLat L Λ → ∀ κ : GA D A, (GlobalTheory.FinPl.Moves A κ L L (· = p.v) ↔ coordHom A p.pr β.b β.b' β.bb' β.b'b κ • Λ = Λ) := by
  intro D k _ _ _ _ p A n _ _ β L Λ hL hΛ κ
  obtain ⟨h1, -, -, h4, -, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p A n β
  obtain ⟨Λ', -, hΛ', hK⟩ := h4 L hL
  have hΛeq : Λ' = Λ := by
    ext x
    rw [hΛ' x, hΛ x]
  subst hΛeq
  obtain ⟨hv, hvAt, h', h'Off, rfl⟩ := (GlobalTheory.FinPlLoc.part_grp (· = p.v) A).1 κ
  obtain ⟨g, rfl⟩ := (h1 hv).1 hvAt
  have hoff : coordHom A p.pr β.b β.b' β.bb' β.b'b h' = 1 := by
    refine Units.ext ?_
    rw [coordHom_val, map_pr_of_grpOff p A h'Off, Matrix.mul_one, β.b'b]
    rfl
  have hg : coordHom A p.pr β.b β.b' β.bb' β.b'b (β.gl g) = g :=
    ((eq_coordHom_iff A p.pr β.b β.b' β.bb' β.b'b (β.gl g) g).1 (β.gl_mat g)).symm
  rw [map_mul, hoff, mul_one, hg, ← hK g]
  constructor
  · intro hm
    refine ⟨hvAt, fun y hy => ?_⟩
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]
  · rintro ⟨-, hm⟩ y hy
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]

end GlobalTheory.FrameMoves

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHalfEqDoubleAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HalfDoubleAnn

theorem frames_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D), ∃ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), (∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k]) ∧ (∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T) := by
  intro D k _ _ _ _ q S T
  obtain ⟨a₀, ha₀, hne, hdiv⟩ := GlobalTheory.T.exists_periodIdeal_local_generator_at_split_point D k q
  set c := q.pr (incA D a₀) with hc
  set G : Matrix (Fin S.rank) (Fin S.rank) k := c • (HSpace.gram S).map (fun a => q.pr (incA D a)) with hG
  have hdet : IsUnit G.det := by
    rw [hG, Matrix.det_smul, isUnit_iff_ne_zero]
    refine mul_ne_zero (pow_ne_zero _ hne) ?_
    have h := (RingHom.map_det (q.pr.comp (incA D)) (HSpace.gram S)).symm
    simp only [RingHom.mapMatrix_apply, RingHom.coe_comp] at h
    change (Matrix.map (HSpace.gram S) (⇑q.pr ∘ ⇑(incA D))).det ≠ 0
    rw [h]
    exact (map_ne_zero_iff _ (q.pr.comp (incA D)).injective).2 (GlobalTheory.FrameCont.gram_det_isUnit S).ne_zero
  let FS : Frame k S.rank (Fin S.rank) := ⟨G⁻¹, G, Matrix.nonsing_inv_mul G hdet, Matrix.mul_nonsing_inv G hdet⟩
  let FT : Frame k T.rank (Fin T.rank) := ⟨1, 1, mul_one 1, mul_one 1⟩
  exact ⟨FS, FT, GlobalTheory.T.stdHomLattice_point_integral_matrix_at_split_place D k q S T c hne hdiv FS FT rfl rfl rfl, GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice D k q S T a₀ ha₀ hne FS FT rfl rfl rfl⟩

variable {D : D7}

theorem symplO_idem_left (S T : HSp D) {e : AE D} {l : WO S T} (hl : IsHalf (cA D e) l) (u : WO S T) :
    symplO S T u l = symplO S T (u.map (e * ·)) l := by
  unfold symplO hO
  congr 2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  have h : cA D (l c b) = e * cA D (l c b) := by
    conv_lhs => rw [← hl c b]
    rw [map_mul, cA_cA]
  rw [Matrix.map_apply]
  conv_lhs => rw [h]
  ring

theorem pr_e {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  have h := q.sec_pr 1
  rw [mul_one] at h
  rw [← h, q.pr_sec, map_one]

theorem mul_idem_of_mem {E₂ : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (hsum : E₂ = ∑ PP ∈ Q, es PP) {PP : Formalism.L2.DIV.Pl D.host.E}
    (hPP : PP ∈ Q) : E₂ * es PP = es PP := by
  rw [hsum, Finset.sum_mul, Finset.sum_eq_single PP]
  · exact (hes PP hPP).1.1
  · intro PP' hPP' hne
    have hs := (hes PP hPP).1
    obtain ⟨v, ε, h1, h2⟩ := hs.2.2
    obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v (es PP) ε hs h1 h2
    have hsum' : IsIdemSum (es PP') {PP'} :=
      ⟨⟨fun _ => es PP', fun P hP => by rw [Finset.mem_singleton] at hP; subst hP; exact hes _ hPP', by simp⟩,
        (hes PP' hPP').1.2.1⟩
    have := OutsideOrth.mul_eq_zero D _ (Place.ofSplitPt q) {PP'} PP (es PP')
      (by rw [Finset.mem_singleton]; exact fun h => hne h.symm) (by rw [show (Place.ofSplitPt q).e = es PP from hq]; exact hes PP hPP) hsum'
    rwa [show (Place.ofSplitPt q).e = es PP from hq] at this
  · intro h; exact absurd hPP h

end GlobalTheory.HalfDoubleAnn

namespace GlobalTheory.HalfDoubleAnn
variable {D : D7}

theorem idem_part_mem (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (E₂ e : AE D)
    (he : IsSplitIdem D e) (hEe : E₂ * e = e) (x : WO S T)
    (H : ∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) →
      ψ (symplO S T x y) = 1) :
    x.map (e * ·) ∈ stdHom S T := by
  obtain ⟨v, ε, h1, h2⟩ := he.2.2
  obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he h1 h2
  subst hq
  obtain ⟨FS, FT, hF1, hF2⟩ := frames_stdHom D _ q S T
  obtain ⟨Λ, -, h2, -, h4, -, h6⟩ := GlobalTheory.SplitSelfDual.selfDual_lattice_split D _ (Place.ofSplitPt q) ψ hψ S T (Fin T.rank) (Fin S.rank) FS FT
  have hdown : ∀ u : WO S T, (Place.ofSplitPt q).down FS FT (u.map (q.e * ·)) = (Place.ofSplitPt q).down FS FT u := by
    intro u
    unfold Place.down
    congr 2
    ext i j
    simp only [Matrix.map_apply]
    have h1 : (Place.ofSplitPt q).π q.e = 1 := pr_e q
    rw [map_mul, h1, one_mul]
  have hhalf : ∀ u : WO S T, IsHalf q.e (u.map (q.e * ·)) := fun u i j => by
    rw [Matrix.map_apply, ← mul_assoc, he.1]
  set y := x.map (q.e * ·) with hy
  by_contra hyn
  have hyup : (Place.ofSplitPt q).up FS FT ((Place.ofSplitPt q).down FS FT y) = y := Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x)
  have hnint : ¬ ∀ r s, (Place.ofSplitPt q).down FS FT y r s ∈ 𝒪[_] := fun hint => hyn (hyup ▸ hF2 _ hint)
  have hyΛ : y ∉ Λ := fun hm => hnint ((h4 _).1 (hyup.symm ▸ hm))
  obtain ⟨l, hlΛ, hlc, hl⟩ := h2 y (hhalf x) hyΛ
  have hlc' : IsHalf (cA D q.e) l := hlc
  have hlE : IsHalf (cA D E₂) l := fun i j => by
    rw [← hlc' i j, ← mul_assoc, ← map_mul, hEe]
  have key := H l hlE fun x' hx' _ => by
    rw [symplO_idem_left S T hlc' x', ← Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x'), hdown]
    exact h6 l hlΛ hlc _ (hF1 x' hx')
  rw [symplO_idem_left S T hlc' x, GlobalTheory.SplitScalar.symplO_skew] at key
  have := GlobalTheory.SplitSelfDual.psi_neg_eq_one key
  rw [neg_neg] at this
  exact hl this

theorem mem_of_ann_ann : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ x : WO S T, IsHalf E₂ x → (∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) → ψ (symplO S T x y) = 1) → x ∈ stdHom S T := by
  intro D ψ hψ S T Q E₂ hE x hx H
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hE
  have hx' : x = ∑ PP ∈ Q, x.map (es PP * ·) := by
    ext i j
    rw [Matrix.sum_apply, ← hx i j, hsum, Finset.sum_mul]
    rfl
  rw [hx']
  exact AddSubgroup.sum_mem _ fun PP hPP =>
    idem_part_mem ψ hψ S T E₂ (es PP) (hes PP hPP).1 (mul_idem_of_mem hes hsum hPP) x H

end GlobalTheory.HalfDoubleAnn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QTw.StepChar

open Formalism.L2.Col Formalism.L2.DIV
open Formalism.L2.Host (HChar)

theorem locK_unif {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L)) (hu : χ.UnrAt Q) (k : Lˣ)
    (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) : χ.locK Q k = χ.val Q :=
  χ.val_eq hu _ ((Formalism.UG.P.levelaf_valued_algebraMap Q (k : L)).trans hk)

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}

theorem g_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (P : rowSG Pr sel mu)
    (hP : P.1 ∉ Pr.vGs) (k : Fin 2) : ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hlp.1.1 (fun h => hlp.2 hP (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)

theorem res_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (hx : (x : X.E) = (y : X.E))
    (hc : (c : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal y) :
    σ ((resChar (mu : Chr X.F X.E X.K) P.1 c : X.Kˣ) : X.K) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ) := by
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hu : P.1.valuation X.E (x : X.E) = 1 := by
    rw [hx]
    exact GlobalTheory.NormOneUnit.val_eq_one fun hy => c.ne_zero (hc.trans (Ideal.Quotient.eq_zero_iff_mem.2 hy))
  have e1 : (m0 j * ξ).locK P.1 x = (m0 j).locK P.1 x * ξ.locK P.1 x := rfl
  rw [e1, GlobalTheory.NormOneUnit.locK_unr ((ht.mu0 j).unr _ (g_notMem hX hPr hsel hg P hP)) hu, one_mul,
    GlobalTheory.NormOneUnit.resChar_eq h hta P.1 c y x hx hc.symm]

theorem map_muAt (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hQ : cst.muq (j.1 + 1) P = (((Ch.muVal j P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) (a : X.Eˣ) :
    σ (muAt Ch sel mu cst j.1 P (a : X.E)) = (((m0 j * ξ).locK P.1 a : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hq := (GlobalTheory.TwistVal.main X.F X.E X.K σ _ ξ h hta P.1).2 hlp.1.2
  have hg' := g_notMem hX hPr hsel hg P hP
  have hm : ∀ x, (((m0 j * ξ)⁻¹.locK P.1 x : ℂˣ) : ℂ) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ)⁻¹ := fun x => by
    rw [← Units.val_inv_eq_inv_val]
    rfl
  rw [← hm]
  refine GlobalTheory.LocCharComp.locChar_eq_locK X.E X.K σ P.1 (m0 j * ξ)⁻¹ _ _ hlp.1.2 (fun q hq' => ?_) (fun x y c hx hc => ?_) a
  · have e1 : (m0 j * ξ).locK P.1 q = (m0 j).locK P.1 q * ξ.locK P.1 q := rfl
    rw [hm, e1, Units.val_mul, ← hq q hq', hQ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul,
      map_inv₀, map_inv₀, ht.muVal j P.1 hg', ← locK_unif (m0 j) P.1 ((ht.mu0 j).unr _ hg') q
        (hq' ▸ GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hlp.1.2), mul_inv]
    rfl
  · rw [hm, if_neg hP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, res_eq hX hPr hsel hg ht h j P hP x y c hx hc]

end General

theorem comp_eq_muAt_and_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  intro B X I hI l Z a P hP k _ _ _ _ q hq hint hden i hi χ hχ μ hμ
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hμ' : (ofSplit q).IsComp χ μ⁻¹ := fun x b hb => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hμ x b hb, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]
  constructor
  · intro x u hu
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA (I.rec7 l Z))).map_zero)
    have h1 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q hq hχ hx0 u hu
    have h2 := map_muAt hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP
      ((hI.idx_ok a).muqQ i hi P hP) (Units.mk0 x hx0)
    have h3 := hμ u (GlobalTheory.LocMod.SplitHecke.idlU q u) rfl
    rw [MonoidHom.inv_apply, Circle.coe_inv, h1] at h3
    exact h3.trans h2.symm
  · have hr : IsRes (D := I.rec7 l Z) (I.C.mu0 ⟨i, hi⟩ * I.xi a) P.1
        ((Units.map (B.embLL : B.fields.K →* ℂ)).comp (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) P.1)) :=
      fun y x c hx hc => Units.ext (res_eq hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP x y c hx hc)
    have ht := (GlobalTheory.LocMod.SplitHecke.tame_and_res (I.rec7 l Z) k q P.1 hq hint hden χ _ _ μ⁻¹ hχ hr hμ').1
    intro x hx
    have := ht x hx
    rwa [MonoidHom.inv_apply, inv_eq_one] at this

end GlobalTheory.QTw.StepChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainFockVectorLevelLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem levelLaw : ∀ D : D7, LevelLaw D := by
  intro D hgap c hc k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.thetaChainStep_vector_twoLevel_law D hgap c hc k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LiftVol

theorem thetaKO_sum_translates {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by
  simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option maxHeartbeats 1000000 in

theorem lift_levelP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t j, j + 1 < D.R.m → ∀ (F : CP (pk W) (lvP W) t (j + 1)) (hF : F.1 ∈ (pk W).CC t (j + 1)), ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) ((pk W).vac j) v → ∀ Q x, liftS ((pk W).ωY t j) ((pk W).νY t (j + 1)) ((pk W).fdY t (j + 1)) (F.1 x) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q) = (Nat.card (lvP W).H : ℂ) • ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF v hv Q x
  have hio : Lift.IsIo ((pk W).νY t (j + 1)) ((pk W).fdY t (j + 1)) (thetaKO ((pk W).ωY t j)) ((pk W).ptY t j)
      ((pk W).ItY j) ((pk W).CC t (j + 1)) ((pk W).CC t j) ((pk W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (pk W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (lvP W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.T.exists_level_elements_step_vector W hW t j hj
  funext g
  unfold liftS Lift.liftInt
  rw [hsum v hv Q]
  simp_rw [thetaKO_sum_translates]
  have hint : ∀ p ∈ (Finset.univ : Finset (lvP W).H), IntegrableOn (fun h => (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ hint]
  have e : ∀ p ∈ (Finset.univ : Finset (lvP W).H), ∫ h in (pk W).fdY t (j + 1), (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h ∂(pk W).νY t (j + 1) =
      ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) g := by
    intro p _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have h1 := hio.eq ⟨F.1, hF⟩ Q x (g * κ p)
    simp only [Lift.liftInt] at h1
    rw [h1, _root_.GlobalTheory.T.chain_projection_level_character W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]
    rw [← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p)), one_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul, Pi.smul_apply, smul_eq_mul]

set_option maxHeartbeats 800000 in

theorem lift_eq_cI_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → ∀ t j, j + 1 < D.R.m → ∀ (G : (f.t t).CC (j + 1)) P v, liftS ((f.t t).om j) (f.c.vol (j + 1)).μ (f.c.vol (j + 1)).𝓕 (G.1 v) ((f.t t).pt j P) = (f.t t).cI j • ((f.t t).io j G).1 (f.c.It j P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j hj G P v
  have h3 := hP.bot.hyp.2.2.2.1
  have hch : (pk W).IsChain := h3.chain
  have hmod : (pk W).IsModels := h3.models
  obtain ⟨h, hio⟩ := (hR.row t).io j hj G
  have hstep := (hR.row t).vP j hj
  have hk := lift_levelP W hP t j hj G h
  have hk' := hk _ hstep P v
  have hω := hch.ωY t j hj
  have hθ : IsInfFam (pk W).θ := hmod.inf
  have hpt := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (cart ((pk W).MY j)) (onb ((pk W).MY j))
    (cart ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1)))
    (GlobalTheory.VecTheta.isThetaFunO_stepVec hstep) P

  have hvol := hR.meas.vol t j hj
  have hκ := hR.meas.κ (j + 1)
  have hHF : ((pk W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    by_cases h2 : j + 1 + 1 < D.R.m
    · have h4 := hmod.νY t (j + 1) h2
      exact ⟨h4.1.1, h4.2⟩
    · have h4 := hmod.νY' t
      have e : D.R.m - 1 = j + 1 := by omega
      rw [e] at h4
      exact ⟨h4.1.1, h4.2⟩

  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 G.2)
  have hleft : ∀ (w : SmT ((pk W).MY (j + 1))), ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, G.1 w (γ * x) = G.1 w x := by
    intro w γ hγ x
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (hm.aut w).left γ hγ x
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add, Pi.add_apply, ha, ha']
  have hthL : ∀ g, ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, (pk W).ωY t j (g, γ * x) ((f.t t).pt j P) 0 =
      (pk W).ωY t j (g, x) ((f.t t).pt j P) 0 := by
    intro g γ hγ x
    have e : ((g, γ * x) : GA D (Yc D j) × GA D (Yc D (j + 1))) = (1, γ) * (g, x) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have : IsTopologicalGroup (GA D (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D (Yc D (j + 1))) := ⟨rfl⟩
  have : Countable (GQ (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Yc D (j + 1)).gram
  have hvol' : (f.c.vol (j + 1)).μ = ENNReal.ofReal (f.g.κ (j + 1) * GlobalTheory.Fam.volLev (pk W) f.g t j) • (pk W).νY t (j + 1) := hvol
  have : (f.c.vol (j + 1)).μ.IsHaarMeasure := (f.c.vol (j + 1)).haar
  have hF₁ := (f.c.vol (j + 1)).fund
  have hF₂ : IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) (f.c.vol (j + 1)).μ :=
    hHF.2.mono (by rw [hvol']; exact Measure.smul_absolutelyContinuous)
  funext g
  rw [liftS_apply, hF₁.setIntegral_eq hF₂ (fun γ x => by
    show (pk W).ωY t j (g, (γ : GA D (Yc D (j + 1))) * x) ((f.t t).pt j P) 0 * G.1 v ((γ : GA D (Yc D (j + 1))) * x) = _
    rw [hthL g γ γ.2 x, hleft v γ γ.2 x])]
  rw [hvol', Measure.restrict_smul, integral_smul_measure]
  have hk2 := congrFun hk' g
  rw [liftS_apply] at hk2

  have hv0 : 0 ≤ GlobalTheory.Fam.volLev (pk W) f.g t j := by
    unfold GlobalTheory.Fam.volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : 0 ≤ f.g.κ (j + 1) * GlobalTheory.Fam.volLev (pk W) f.g t j := mul_nonneg hκ.le hv0
  rw [ENNReal.toReal_ofReal hc0]
  erw [hk2]
  show _ = (cIOf (pk W) (lvP W) f.g t j • ((f.row t).io j G).1 ((pk W).ItY j P v)) g
  rw [hio]
  simp only [Pi.smul_apply, cIOf, Complex.real_smul, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.Fam.LiftVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTraceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportCorrection_carries_columnLattice_rowTrace : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff | exact GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff | (intros; apply GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionInvariantPairFunctionalResidueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionInvariant_pair_functional_residue : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 2 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → ∃ ε : 𝓀[k], ε ≠ 0 ∧ ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * ε) := by
  first | exact @GlobalTheory.latPair_hasVal_residue_of_transvections | exact GlobalTheory.latPair_hasVal_residue_of_transvections | (intros; apply GlobalTheory.latPair_hasVal_residue_of_transvections <;> assumption)
end

