import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0661
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0662
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiFlatMapEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFlatMap_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  first | exact @GlobalTheory.AscFlatEqui.flBF_equivariant | exact GlobalTheory.AscFlatEqui.flBF_equivariant | (intros; apply GlobalTheory.AscFlatEqui.flBF_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BplusEqCoef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem bplus_eq_coef {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus W M φ F = ∫ h in M.fd (.top 0), φ h *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F (embTop G h) ∂M.ν (.top 0) := by
  simp only [Bplus, besInt, GlobalTheory.Mem.TrueRecord.coef, ← integral_const_mul, mul_assoc]

theorem nu_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {M M' : Vol G}
    (hM : M.IsRow) (hM' : M'.IsRow) : M.ν (.top 0) = M'.ν (.top 0) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have h1 := hM.top
  have h2 := hM'.top
  unfold Vol.IsAt at h1 h2
  have hz : Node.neg D.R.m (Node.top 0) = 0 := rfl
  rw [if_pos hz] at h1 h2
  haveI := h1.1.1
  haveI := h2.1.1
  have e := Measure.isMulLeftInvariant_eq_smul (M.ν (.top 0)) (M'.ν (.top 0))
  have a1 := GlobalTheory.Mass.Levels.measure_comap_finE h1.1
  have a2 := GlobalTheory.Mass.Levels.measure_comap_finE h2.1
  have hc : Measure.haarScalarFactor (M.ν (.top 0)) (M'.ν (.top 0)) = 1 := by
    rw [e, Measure.smul_apply, a2] at a1
    simpa using a1
  rw [e, hc, one_smul]

theorem bplus_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (M M' : Vol G),
    M.IsRow → M'.IsRow → ∀ φ F, GlobalTheory.Unf.IsContAut _ φ → GlobalTheory.Unf.IsContAut _ F → Bplus W M φ F = Bplus W M' φ F := by
  intro D T L sc G W M M' hM hM' φ F hφ hF
  have hψ := W.ψ_std
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hF' : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g := hF.1
  have hN := hM.unip
  have hN' := hM'.unip
  rw [bplus_eq_coef, bplus_eq_coef]
  have ec : ∀ g, GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F g =
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F g := fun g =>
    GlobalTheory.Mem.TrueRecord.coef_eq hψ hι G.besTop hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 hF' g
  simp only [ec]
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hf1 := (hM.top.haar_fund).2
  have hf2 := hM'.top.haar_fund
  rw [nu_top_eq hM hM'] at hf1 ⊢
  haveI := hf2.1
  set d := G.rowDec 0 (by have := D.R.two_le_m; omega)
  have e0 : ∀ h, embTop G h = stabilizerEmbedding d h := fun h => rfl
  have e1 : stabilizerEmbedding d 1 = 1 := by
    have := GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d 1 1
    rw [one_mul] at this
    exact left_eq_mul.mp this
  refine hf1.setIntegral_eq hf2.2 fun γ h => ?_
  have hγ : (γ : GA D (G.V (.top 0))) ∈ GQ (G.V (.top 0)) := γ.2
  have hinv : stabilizerEmbedding d (γ : GA D (G.V (.top 0)))⁻¹ = (stabilizerEmbedding d γ)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel, e1]
  have r1 : EmbRel _ _ d.ι (stabilizerEmbedding d γ) γ := (embRel_iff d _ _).2 rfl
  have r2 : EmbRel _ _ d.ι (stabilizerEmbedding d γ)⁻¹ (γ : GA D (G.V (.top 0)))⁻¹ := hinv ▸ (embRel_iff d _ _).2 rfl
  change φ ((γ : GA D (G.V (.top 0))) * h) *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F (embTop G ((γ : GA D (G.V (.top 0))) * h)) = _
  rw [hφ.1 _ hγ, e0, e0, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul,
    GlobalTheory.Mem.TrueRecord.coef_left hψ hι G.besTop hN'.1 hN'.2.1 hN'.2.2 hF' (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational d _ hγ) r1 r2]

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefProd
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def colCoef (ch : Choice R) (t : T) (β : CosFam ch.G t) (j : ℕ) : ℚ :=
  ∏ w : locPl ch.G t, if h : j < D.R.m then
    invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) else 1

theorem coef_prod (ch : Choice R) (t : T) (Φ : ch.G.Datum) (β : CosFam ch.G t) :
    ∏ w, ((ch.S.term t Φ β w).coef : ℂ) = ((idx D).map fun j => (colCoef ch t β j : ℂ)).prod := by
  have hw : ∀ w, (ch.S.term t Φ β w).coef = ∏ i : Fin (D.R.m - 2), (if h : 1 + (i : ℕ) < D.R.m then
      invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := 1 + (i : ℕ)) h) else 1) := by
    intro w
    have hj : ∀ (j j' : ℕ) (_ : j = j') (h : j < D.R.m) (h' : j' < D.R.m),
        invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) =
          invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j') h') := by
      rintro j _ rfl h h'
      rfl
    show ∏ i : Fin (D.R.m - 2), invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w))
      (j := (i : ℕ) + 1) (show (i : ℕ) + 1 < D.R.m by have := i.isLt; omega)) = _
    exact Finset.prod_congr rfl fun i _ => by
      rw [dif_pos (show 1 + (i : ℕ) < D.R.m by have := i.isLt; omega)]
      exact hj _ _ (Nat.add_comm _ _) _ _
  have key : ∏ w, (ch.S.term t Φ β w).coef = ((idx D).map fun j => colCoef ch t β j).prod := by
    simp only [hw]
    rw [Finset.prod_comm]
    simp only [idx, List.range'_eq_map_range, List.map_map]
    rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => rfl
  have := congrArg (Rat.cast : ℚ → ℂ) key
  rw [Rat.cast_prod, Rat.cast_list_prod, List.map_map] at this
  exact this

end GlobalTheory.RowWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColconSplitFamAppend
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.Unf

theorem colcon_splitFam_append {T : Type} {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : p.Fam S) (e : q.Fam S), splitFam q (Path.Fam.append (q := q) d e) = (d, e)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
      show ((splitFam q (Path.Fam.append (q := q) d e.1)).1, ((splitFam q (Path.Fam.append (q := q) d e.1)).2, e.2)) = (d, e)
      rw [colcon_splitFam_append q d e.1]
      rfl

theorem colcon_getD_downFam {T : Type} {S : Arrow T → Type} (t : T) (i : ℕ) :
    ∀ (n : ℕ) (f : ∀ j : Fin n, S (.down t i j)) (j : ℕ) (hj : j < n), getD t i n (downFam t i n f) j hj = f ⟨j, hj⟩
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, j, hj => by
      unfold getD
      have hs := colcon_splitFam_append (p := Path.one (.down t i n)) (downPath t i n) ((), f (Fin.last n))
        (downFam t i n fun j => f j.castSucc)
      rw [downFam]
      split_ifs with h
      · erw [hs]
        exact colcon_getD_downFam t i n _ j h
      · obtain rfl : n = j := by omega
        erw [hs]
        rfl

theorem colcon_nIter_congr {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
    {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) {q q' : (∀ i, H i) → ℂ} :
    ∀ (l : List ι) (h : ∀ i, H i) (z : ℂ), NIter ρ μ q l h z →
      (∀ h' : ∀ i, H i, (∀ i, i ∉ l → h' i = h i) → q h' = q' h') → NIter ρ μ q' l h z
  | [], h, z, hz, hq => (show z = q h from hz).trans (hq h fun _ _ => rfl)
  | i :: l, h, z, ⟨f, hf, hr⟩, hq => ⟨f, hf, fun g => colcon_nIter_congr ρ μ l _ _ (hr g) fun h' hh' => hq h' fun k hk => by
      rw [hh' k fun hl => hk (List.mem_cons_of_mem _ hl), Function.update_of_ne fun e => hk (by simp [e])]⟩

theorem colcon_quot {G : Type} [Group G] [MeasurableSpace G] {R R' : Subgroup G} (e : R = R') {ρ : Measure R} {ρ' : Measure R'}
    (hh : HEq ρ ρ') {μ : Measure G} {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 ρ' μ f z) : IsQuotIntL1 ρ μ f z := by
  subst e
  obtain rfl := eq_of_heq hh
  exact h

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem colcon_rowGrp_jac {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (jacAt G hM j σ hj).d := by
  unfold rowGrp
  rw [dif_pos (by omega)]
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  rfl

theorem colcon_rowGrp_bes {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m)
    (vN : VolN (besDecAt G j σ hj)) :
    rowGrp G j = besGrp (besAt G hM j σ hj vN).d (besAt G hM j σ hj vN).o := by
  unfold rowGrp
  rw [dif_neg (by omega), dif_pos (by omega)]
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  rfl

theorem colcon_gen (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t)
    (F : Fn G (.grid D.R.m D.R.m)) (ρ : ∀ j, Measure (rowGrp G j))
    (hJ : ∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR)
    (hB : ∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) (h : Pts G) (g : GA D (G.V (.grid D.R.m j)))
      (φ : GA D (G.V (.top j)) → ℂ) (z : ℂ), g = h j →
      (chainFrom G W t hM σ j hj vN).Iter
        (colPer W hM σ j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) σ j hj vN) F φ g) z →
      NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h' => jPer W M t (conAt W hM Φ h') F σ j hj φ)
        (List.range' (j + 1) (2 * σ)) h z
  | 0, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hc : conAt W hM Φ h j = lastDat W hM j hj vN (h j) (Φ ⟨j, by omega⟩)
          (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)) := by
        unfold conAt
        rw [dif_pos hj]
        rfl
      have hz' : z = colPer W hM 0 j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) 0 j hj vN) F φ (h j) () := hz
      show z = jPer W M t (conAt W hM Φ h) F 0 j hj φ
      rw [hz']
      show _ = ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j φ (conAt W hM Φ h j)
        (GlobalTheory.RowChain.topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
      rw [hc]
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom]
      rw [colcon_getD_downFam, colcon_getD_downFam]
      rfl
  | σ + 1, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      obtain ⟨f₁, f₂, h1, h2⟩ := hz
      have hl : List.range' (j + 1) (2 * (σ + 1)) = (j + 1) :: (j + 1 + 1) :: List.range' (j + 1 + 1 + 1) (2 * σ) := by
        rw [show 2 * (σ + 1) = 2 * σ + 1 + 1 by ring, List.range'_succ, List.range'_succ]
      rw [hl]
      refine ⟨f₁, colcon_quot (colcon_rowGrp_jac hM (j + 1) (σ + 1) (by omega)) (hJ _ _ _) h1, fun a => ?_⟩
      refine ⟨f₂ a, colcon_quot (colcon_rowGrp_bes hM (j + 1 + 1) σ (by omega) _) (hB _ _ (by omega)) (h2 a).1,
        fun b => ?_⟩
      have hi := (h2 a).2 b
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom] at hi
      have ih := colcon_gen G W t hM Φ F ρ hJ hB σ (j + 1 + 1) (by omega) _
        (Function.update (Function.update h (j + 1) a) (j + 1 + 1) b) b _ (f₂ a b) (by simp) hi
      refine colcon_nIter_congr _ _ _ _ _ ih fun h' hh' => ?_
      have e0 : h' j = h j := (hh' j (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _))
      have e1 : h' (j + 1) = a := (hh' (j + 1) (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_self _ _ _))
      have e2 : h' (j + 1 + 1) = b := (hh' (j + 1 + 1) (by simp only [List.mem_range'_1]; omega)).trans (Function.update_self _ _ _)
      show _ = jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) _ (biL W M t j φ (conAt W hM Φ h' j))
      congr 1
      have hx : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
      have hC : conAt W hM Φ h' j = _ :=
        (dif_neg (show ¬ (j + 2 * 0 + 2 = D.R.m) by omega)).trans (dif_pos hx)
      rw [hC]
      obtain rfl : σ = (D.R.m - 4 - j) / 2 := by omega
      rw [e0, e1, e2, colcon_getD_downFam, colcon_getD_downFam]
      rfl

theorem nIter_conAt_of_colPer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t) (F : Fn G (.grid D.R.m D.R.m)) (φ : Fn G (.top 0)) (z : ℂ), (chain G W t hM).Iter (colPer W hM _ 0 top_idx (topVN hM) (chainData G W t hM (downFam t D.R.m D.R.m Φ)) F φ 1) z → ∀ (ρ : ∀ j, Measure (rowGrp G j)), (∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR) → (∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) → NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h => jPer W M t (conAt W hM Φ h) F _ 0 top_idx φ) (idx D) 1 z := by
  intro D T L sc G W t M hM Φ F φ z hz ρ hJ hB
  have e : List.range' (0 + 1) (2 * ((D.R.m - 2) / 2)) = idx D := by
    unfold idx
    have := top_idx (D := D)
    congr 1
    omega
  rw [← e]
  exact colcon_gen G W t hM Φ F ρ hJ hB _ 0 top_idx (topVN hM) 1 1 φ z rfl hz

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

theorem level_datum_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∃ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q ∧ IdemTwo Lv.w ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Irow := GlobalTheory.T.frameAdjoint_partAt_movedRationalPoint_row D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iint := GlobalTheory.T.latticeVector_adjointRow_integral D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iker := GlobalTheory.T.adjointFrameRowReduction_eq_zero_iff_mem D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Isurj := GlobalTheory.T.rowReduction_surjective_latticeVectors_places D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Ilin := GlobalTheory.T.adjointFrameRowReduction_conjLinear_integers D T βT a e
  set R := GlobalTheory.LiftDat.rowRed T βT a e with hR
  have hz : ∀ PP, R PP 0 = 0 := by
    intro PP
    have hi := Iint 0 (zero_mem _)
    have h := (Ilin PP 0 0 hi hi 1).2
    simp only [smul_zero, add_zero, map_one, one_mul] at h
    funext j
    have h' := congrFun h j
    simp only [Pi.zero_apply]
    linear_combination -h'
  have hsum : ∀ PP (s : Finset (Fin T.rank)) (c : Fin T.rank → 𝓞 D.host.E)
      (u : Fin T.rank → Fin T.rank → D.host.E) (v : Fin T.rank → D.host.E), (∀ j, u j ∈ C.X.Λ) → v ∈ C.X.Λ →
      R PP (∑ j ∈ s, c j • u j + v) = fun l => ∑ j ∈ s, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c j)) *
        R PP (u j) l + R PP v l := by
    intro PP s c u v hu hv
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have hm : ∑ j ∈ s, c j • u j + v ∈ C.X.Λ := add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hu j)) hv
      rw [Finset.sum_insert hj, add_assoc]
      rw [show c j • u j = ((c j : D.host.E)) • u j from rfl]
      rw [(Ilin PP (u j) _ (Iint _ (hu j)) (Iint _ hm) (c j)).2, ih]
      funext l
      rw [Finset.sum_insert hj]
      ring
  choose β hβΛ hβred using fun j : Fin T.rank => Isurj (fun PP => Pi.single j 1)
  have hexp : ∀ PP ∈ Pg ∪ Q, ∀ (c : Fin T.rank → 𝓞 D.host.E) (w : Fin T.rank → D.host.E), w ∈ C.X.Λ →
      ∀ l, R PP (∑ j, c j • β j + w) l = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c l)) + R PP w l := by
    intro PP hPP c w hw l
    rw [hsum PP Finset.univ c β w hβΛ hw]
    simp only [hβred _ PP hPP, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
    intro v hv
    choose c hc using fun j => GlobalTheory.T.exists_integer_conj_prescribed_residues_places D (Pg ∪ Q) (fun PP => R PP v j)
    have hw : v - ∑ j, c j • β j ∈ C.X.Λ := sub_mem hv (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have hw0 : v - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      refine (Iker _ hw).1 fun PP hPP => ?_
      funext l
      have h := hexp PP hPP c _ hw l
      rw [add_sub_cancel, hc l PP hPP] at h
      simp only [Pi.zero_apply]
      linear_combination -h
    have e1 : v = ∑ j, c j • β j + (v - ∑ j, c j • β j) := by abel
    rw [e1]
    exact Submodule.add_mem_sup (sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) hw0
  obtain ⟨Lv0, hw⟩ := GlobalTheory.Ker.Base.exists_level C.X
  have hle : ∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftLevel.liftI Pg Q ≤ conjI PP.asIdeal := fun PP h => GlobalTheory.LiftDat.liftI_le h
  have hnot : ∀ PP ∈ Pg ∪ Q, ∀ s : 𝓞 D.host.E, IsCoprime (Ideal.span {s}) (GlobalTheory.LiftLevel.liftI Pg Q) →
      GlobalTheory.SW.Lev.bar s ∉ PP.asIdeal := by
    intro PP hPP s hs hmem
    obtain ⟨x, m, hm, hxm⟩ := GlobalTheory.SW.Lev.cop_iff.1 hs
    have h1m : (1 : 𝓞 D.host.E) ∈ conjI PP.asIdeal := by
      rw [← hxm]
      exact add_mem (Ideal.mul_mem_left _ _ (GlobalTheory.SW.Lev.mem_conjI.2 hmem)) (hle PP hPP hm)
    have := GlobalTheory.SW.Lev.mem_conjI.1 h1m
    rw [map_one] at this
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hind : ∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 →
      ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
    intro d ⟨s, hs, hsm⟩ j
    rw [sub_zero, Finset.smul_sum] at hsm
    have e2 : ∑ j, s • d j • β j = ∑ j, (s * d j) • β j + 0 := by
      rw [add_zero]; exact Finset.sum_congr rfl fun j _ => (mul_smul _ _ _).symm
    rw [e2] at hsm
    refine GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place D Pg Q _ fun PP hPP => ?_
    have h0 := hexp PP hPP (fun j => s * d j) 0 (zero_mem _) j
    have hmemΛ : ∑ j, (s * d j) • β j + 0 ∈ C.X.Λ :=
      add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j)) (zero_mem _)
    rw [(Iker _ hmemΛ).2 hsm PP hPP, hz] at h0
    simp only [Pi.zero_apply, add_zero, map_mul] at h0
    have h0' : GlobalTheory.SW.Lev.bar s * GlobalTheory.SW.Lev.bar (d j) ∈ PP.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_mul]; exact h0.symm)
    rcases PP.isPrime.mem_or_mem h0' with h | h
    · exact absurd h (hnot PP hPP s hs)
    · exact GlobalTheory.SW.Lev.mem_conjI.2 h
  refine ⟨GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0, rfl, hw, ?_, ?_⟩
  · intro κ hκ κ' hκ' PP hPP i j
    have hm := GlobalTheory.LiftDat.mem_Jgrp.1 hκ PP hPP
    have hij := congrArg (fun g : GL (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal) => g.val i j) hm
    have hk := congrFun (congrFun hκ' i) j
    change (GlobalTheory.LiftDat.toConj Pg Q PP (Finset.mem_union_left _ hPP)) (κ.val i j) =
      (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j at hij
    simp only [Matrix.map_apply] at hk
    rw [← hk] at hij
    have hij2 : Ideal.Quotient.mk (conjI PP.asIdeal) (κ' i j) =
        (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j := hij
    rw [← Ideal.Quotient.eq, hij2]
    by_cases hij' : i = j
    · subst hij'; simp
    · simp [Matrix.one_apply_ne hij']
  · intro y hy
    have hrow : ∀ i, y i ∈ C.X.Λ := by
      intro i
      have key : ∀ z ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI (GlobalTheory.LiftLevel.liftI Pg Q)) • C.X.Λ),
          z i ∈ C.X.Λ := by
        intro z hz
        induction hz using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨v, hv, u, hu, rfl⟩ := hz
          have hvi : IsIntegral ℤ (v i) := (GlobalTheory.SW.Base.mem_stdL _).1 hv i
          have : vecMulVec v u i = (⟨v i, hvi⟩ : 𝓞 D.host.E) • u := by
            funext k; rw [vecMulVec_apply, Pi.smul_apply, Algebra.smul_def]; rfl
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.smul_le_right hu)
        | zero => exact zero_mem _
        | add x y _ _ hx hy => exact add_mem hx hy
        | neg x _ hx => exact neg_mem hx
      exact key y hy
    have hdec : ∀ i, ∃ c : Fin T.rank → 𝓞 D.host.E, y i - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      intro i
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hsp (hrow i))
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hp
      refine ⟨c, ?_⟩
      rw [hc, ← hpq, add_sub_cancel_left]
      exact hq
    choose c hc using hdec
    refine GlobalTheory.T.levelDatum_conjugatePlacesLevel_eq_characters D S T C hn Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0 hind y c hc _ ?_
    intro PP hPP i j
    rw [Irow]
    have hw : y i - ∑ j, c i j • β j ∈ C.X.Λ := sub_mem (hrow i) (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have h := hexp PP hPP (c i) _ hw j
    rw [add_sub_cancel, (Iker _ hw).2 (hc i) PP hPP, Pi.zero_apply, add_zero] at h
    exact h

end GlobalTheory.LiftDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  first | exact @GlobalTheory.CosDual.cosDual | exact GlobalTheory.CosDual.cosDual | (intros; apply GlobalTheory.CosDual.cosDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f ∈ G.M.Pol B.ψ B.emb,
      δ f ∈ G.M.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  first | exact @GlobalTheory.OscLie.exists_lie_deriv_pol | exact GlobalTheory.OscLie.exists_lie_deriv_pol | (intros; apply GlobalTheory.OscLie.exists_lie_deriv_pol <;> assumption)
end

