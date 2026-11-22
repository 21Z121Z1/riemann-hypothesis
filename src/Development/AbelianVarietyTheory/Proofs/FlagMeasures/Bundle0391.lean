import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0224

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairGramInvariantUnchangedIsometry
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

private theorem sum_castLE_lemma {M : Type} [AddCommMonoid M] {l N : ℕ} (h : l ≤ N) (g : Fin N → M)
    (hg : ∀ a : Fin N, l ≤ (a : ℕ) → g a = 0) :
    ∑ a, g a = ∑ a : Fin l, g (Fin.castLE h a) := by
  symm
  calc ∑ a : Fin l, g (Fin.castLE h a) = ∑ x ∈ Finset.univ.map (Fin.castLEEmb h), g x :=
        (Finset.sum_map Finset.univ (Fin.castLEEmb h) g).symm
    _ = ∑ a, g a := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a _ ha
        apply hg
        by_contra hlt
        exact ha (Finset.mem_map.2 ⟨⟨(a : ℕ), Nat.lt_of_not_le hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem leadMinorE_unitri_both {E : Type} [Field E] {N : ℕ} (Z U U' : Matrix (Fin N) (Fin N) E)
    (hU : IsUpUni U) (hU' : IsUpUni U') (l : ℕ) :
    leadMinorE (U.transpose * Z * U') l = leadMinorE Z l := by
  have hz : ∀ i j : Fin N, j < i → U i j = 0 := fun i j hij => (hU i j).1 hij
  have hz' : ∀ i j : Fin N, j < i → U' i j = 0 := fun i j hij => (hU' i j).1 hij
  unfold leadMinorE
  by_cases h : l ≤ N
  · rw [dif_pos h, dif_pos h]
    have key : (U.transpose * Z * U').submatrix (Fin.castLE h) (Fin.castLE h) =
        (U.submatrix (Fin.castLE h) (Fin.castLE h)).transpose * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
          U'.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [sum_castLE_lemma h]
      · refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [sum_castLE_lemma h]
        intro a ha
        have hi := i.isLt
        rw [hz a (Fin.castLE h i) (by rw [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
      · intro b hb
        have hj := j.isLt
        rw [hz' b (Fin.castLE h j) (by rw [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
    have t1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have t2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU' (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have d1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t1]
      exact Finset.prod_eq_one (fun a _ => (hU (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    have d2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t2]
      exact Finset.prod_eq_one (fun a _ => (hU' (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, d1, d2, one_mul, mul_one]
  · rw [dif_neg h, dif_neg h]

theorem gval_eq_of_movesTo : ∀ (D : D7) {T T' : D.host.E} (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F F0' F' ρ U U' h
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hiso : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  have hstar : IsUpUni (U.map star) := by
    refine fun i j => ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [Matrix.map_apply, (hU i j).1 hij, star_zero]
    · rw [Matrix.map_apply, (hU i j).2 hij, star_one]
  have hZ : Formalism.MainNotions.S.Zhat F.fl F'.fl = (U.map star).transpose * Formalism.MainNotions.S.Zhat F0.fl F0'.fl * U' := by
    ext a b
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← hiso (F.fl.fvec a) (F'.fl.fvec b), hF a, hF' b]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, frame, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    ring
  show Formalism.MainNotions.S.Gflag F.fl F'.fl = Formalism.MainNotions.S.Gflag F0.fl F0'.fl
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [hZ, leadMinorE_unitri_both _ _ _ hstar hU', leadMinorE_unitri_both _ _ _ hstar hU']

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevel
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAllKType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  simp only [AutInst.Kg, AutInst.Kset, Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · simp
  · simp [AutInst.fmat]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨h1, hm, hn, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hbi, -⟩ := B.e_adm

  set π : B.I.Gf → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) := fun a => B.R (1, a) with hπ
  have hπ1 : π 1 = 1 := h1
  have hπm : ∀ a b, π (a * b) = π a * π b := fun a b => by
    simp only [hπ]
    rw [← hm]
    congr 1
    ext <;> simp
  have hπn : ∀ a v, ‖π a v‖ = ‖v‖ := fun a v => hn _ v

  have hek : ∀ x, B.e (k * x) = B.e x := fun x => by
    simpa using hbi x k hk 1 (one_mem_Kg B.I B.g)
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  change ⟪x, π k (B.Re y)⟫_ℂ = _
  rw [GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (B.Re y), B.Re_spec.2 (π k⁻¹ x) y, B.Re_spec.2 x y]
  have hinner : ∀ a, ⟪π k⁻¹ x, B.R (1, a) y⟫_ℂ = ⟪x, B.R (1, k * a) y⟫_ℂ := fun a => by
    have := (GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (π a y)).symm
    change ⟪π k⁻¹ x, π a y⟫_ℂ = ⟪x, π (k * a) y⟫_ℂ
    rw [this, hπm, ContinuousLinearMap.mul_apply]
  simp_rw [hinner]
  calc ∫ a, B.e a * ⟪x, B.R (1, k * a) y⟫_ℂ ∂B.μf
      = ∫ a, (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) (k * a) ∂B.μf := by
        congr 1
        ext a
        simp only [hek]
    _ = ∫ a, B.e a * ⟪x, B.R (1, a) y⟫_ℂ ∂B.μf := by
        exact integral_mul_left_eq_self (μ := B.μf) (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hmaj := hint 0 le_rfl (fun v => by
    by_cases hq : rkR (B.I.ε v) = 0
    · exact Or.inl hq
    right

    have hqn : rkR (B.I.ε v) ≤ B.I.n := by
      unfold rkR
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    have hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
    have hqn' : (rkR (B.I.ε v) : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hqn
    have hs : 0 < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hn : 0 < (B.I.n : ℝ) := by linarith
    have hns : 0 < (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := mul_pos hn hs
    have h1 : (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (rkR (B.I.ε v) : ℝ)
        ≤ (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (B.I.n : ℝ) :=
      mul_le_mul_of_nonneg_left hqn' hns.le
    have h2 := hb v
    nlinarith)
  simp only [zero_mul, Real.exp_zero, mul_one] at hmaj
  exact hmaj.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)

theorem cusp_all : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro B d h hd hK hg hh hl hb A hA

  obtain ⟨T0, hT0, hA'⟩ := Submodule.mem_map.1 hA
  have hAe : A = B.Re.comp T0 := by rw [← hA']; rfl
  subst hAe
  have hT0' : ∀ g : B.I.Ginf, T0.comp (B.σs g) = (B.R (g, 1)).comp T0 := hT0
  have hint := integrable_ph B d h hd hl hb
  obtain ⟨-, hcomm, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hHom : ∀ g : B.I.Ginf, (B.Re.comp T0).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp T0) := fun g => by
    rw [ContinuousLinearMap.comp_assoc, hT0' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  refine ⟨hHom, fun u => ?_⟩

  obtain ⟨S, hSmem, hScl, hSinv, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, hirr, -, hnorm, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hw := GlobalTheory.T.countedVectors_are_cuspForms_singleLowestKType B d h hd hK hg hh hl hb T hT (B.Re.comp T0) hA
  let S' : Submodule ℂ B.Hs := S.comap ((B.Re.comp T0 : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund)
  have hS'cl : IsClosed (S' : Set B.Hs) := hScl.preimage (B.Re.comp T0).continuous
  have hS'inv : ∀ g, ∀ v ∈ S', B.σs g v ∈ S' := fun g v hv => by
    have hv' : (B.Re.comp T0) v ∈ S := hv
    show (B.Re.comp T0) (B.σs g v) ∈ S
    have := congrArg (fun F : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => F v) (hHom g)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
    exact hSinv _ _ hv'
  have hwS : B.tens B.w ∈ S' := (hSmem _).2 hw
  rcases hirr S' hS'cl hS'inv with h0 | htop
  · exfalso
    rw [h0, Submodule.mem_bot] at hwS
    rw [hwS, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · have hu : u ∈ S' := htop ▸ Submodule.mem_top
    refine ⟨(hSmem _).1 hu, fun k hk => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re, re_fixed B k hk]

end GlobalTheory.Dec.CuspAllKType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFlagScaledFrameEqBaseChangeFlag
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagBaseChange

theorem isUnit_frFac {D : D7} {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (p : PlF D)
    (A : LocNG.FrameD (locH Z p) D.R.rS) (hA : A.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    (b : Fin D.R.rS) : IsUnit (frFac Z.δ p b.castSucc) := by
  rcases A with ⟨f, es, T0, h1, h2, h3, h4, h5⟩
  dsimp only at hA
  subst hA
  have hb := h4 b b
  dsimp only at hb
  rw [if_pos rfl, (locH Z p).h_smul_left] at hb
  exact ⟨⟨_, _, hb, (mul_comm _ _).trans hb⟩, rfl⟩

theorem span_bcP_Xa_eq_Fj : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (j : ℕ), Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa j : Set (VS D).V)) = (A p).Fj j := by
  intro D T G Z A hA p j
  unfold LocNG.FrameD.Fj LocNG.FrameD.e FlagG.Xa
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      obtain ⟨u, hu⟩ := GlobalTheory.FlagBaseChange.isUnit_frFac G Z p (A p) (hA p) i
      have hmem : (A p).f i.castSucc ∈
          Submodule.span (D.s.atP p).Ep ((fun a : Fin D.R.rS => (A p).f a.castSucc) '' {a : Fin D.R.rS | (a : ℕ) < j}) :=
        Submodule.subset_span ⟨i, hi, rfl⟩
      have hf : (A p).f i.castSucc = frFac Z.δ p i.castSucc • baseChange₂ D p (G.fl.e i) := by
        rw [hA p]
        dsimp only
        rw [Formalism.L2.SG.Pf.frame_castSucc_sat]
      rw [hf, ← hu] at hmem
      have hv := Submodule.smul_mem _ (↑u⁻¹ : (D.s.atP p).Ep) hmem
      rw [smul_smul, Units.inv_mul, one_smul] at hv
      exact hv
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [baseChange_smul₂]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    dsimp only
    rw [hA p]
    dsimp only
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨G.fl.e i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩
    rw [Formalism.L2.SG.Pf.frame_castSucc_sat]

end GlobalTheory.FlagBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalModelsUnsplitAlmostAll
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSplitFinite

theorem finite_resChar_eq (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l ≠ 0) :
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | Formalism.MainNotions.S.Loc.resChar p = l}.Finite := by
  have hx : ((l : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hI : Ideal.span {((l : 𝓞 F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold Formalism.MainNotions.S.Loc.resChar at hp
  rw [← hp]
  exact ringChar.Nat.cast_ringChar

theorem split_finite : ∀ (D : D7) (Z : LocDat D), {p : PlF D | (Z.M p).split ≠ none}.Finite := by
  intro D Z
  have h0 := finite_resChar_eq D.host.F (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := finite_resChar_eq D.host.F (D.host.g 1) (D.host.g_prime 1).ne_zero
  refine (h0.union h1).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    have ha := (Z.agree p).2.2.2.2.2
    revert ha
    cases h : (Z.M p).split with
    | none => exact absurd h hp
    | some g =>
      cases h' : (D.s.atP p).split with
      | none => intro ha; exact ha.elim
      | some sg => intro _; rfl
  have hm := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr hm

end GlobalTheory.LocSplitFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesLeadingMinorEq
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMinor

theorem leadMinor_atBase : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS),
    AtBase Z p F F' Tn T'n P → ∀ l : ℕ, P.Dm l =
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  intro D Z p T T' F F' Tn T'n P hP l
  obtain ⟨hA, hB, -, -⟩ := hP
  have hent : ∀ a b, (locH Z p).Zhat P.A.f P.B.f a b =
      (Z.M p).L.cj (frFac Z.δ p a) * (frFac Z.δ p b *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Zhat F.fl F'.fl a b)) := by
    intro a b
    rw [hA, hB]
    show LocFacts₂ Z.M p (frFac Z.δ p b • baseChange₂ D p (frame F' b)) (frFac Z.δ p a • baseChange₂ D p (frame F a)) = _
    rw [Formalism.L2.SG.Pf.LocFacts.localForm_smul_left₂, Formalism.L2.SG.Pf.LocFacts.localForm_smul_right, baseChangeAt_form Z.M p (Z.hcj p)]
    simp only [Formalism.MainNotions.S.Zhat, frame]
    ring
  show (locH Z p).Dl P.A.f P.B.f l = _
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  split_ifs with hl
  · rw [RingHom.map_det]
    have hM : ((locH Z p).Zhat P.A.f P.B.f).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        Matrix.of fun i j => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * (frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, hent]
    have e1 := Matrix.det_mul_column (fun i : Fin l => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)))
      (Matrix.of fun i j => frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j)
    have e2 := Matrix.det_mul_row (fun j : Fin l => frFac Z.δ p (Fin.castLE hl j))
      (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE)
    simp only [Matrix.of_apply] at e1
    rw [RingHom.mapMatrix_apply, hM, e1, e2, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    set g : ℕ → (D.s.atP p).Ep := fun k => if h : k < D.R.rS + 1 then
      (Z.M p).L.cj (frFac Z.δ p ⟨k, h⟩) * frFac Z.δ p ⟨k, h⟩ else 1 with hg
    have h1 : (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1)
        = ∏ k ∈ Finset.range (D.R.rS + 1), if k < l then g k else 1 := by
      rw [← Fin.prod_univ_eq_prod_range (fun k => if k < l then g k else 1)]
      refine Finset.prod_congr rfl fun a _ => ?_
      show _ = (if a.val < l then g a.val else 1)
      rw [hg]; dsimp only; rw [dif_pos a.isLt]
    have h2 : (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i))
        = ∏ k ∈ Finset.range l, g k := by
      rw [← Fin.prod_univ_eq_prod_range g]
      refine Finset.prod_congr rfl fun i _ => ?_
      have : i.val < D.R.rS + 1 := lt_of_lt_of_le i.isLt hl
      show _ = g i.val
      rw [hg]; dsimp only; rw [dif_pos this]; rfl
    rw [h1, h2, ← Finset.prod_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · simp

end GlobalTheory.LocMinor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRationalPointIsPoint
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocalBlockEntries

open Formalism.L2.SG.Pf.AtPt

theorem ptEntryL_eq' {S : Type} [CommRing S] (L : List (Sˣ × ℕ+)) : ∀ i j : ℕ,
    Formalism.MainNotions.S.Loc.ptEntryL L i j = ptEntry (L.map fun b => ((b.1 : S), (b.2 : ℕ))) i j := by
  induction L with
  | nil => intro i j; rfl
  | cons b L ih =>
    intro i j
    obtain ⟨t, s⟩ := b
    simp only [Formalism.MainNotions.S.Loc.ptEntryL, List.map_cons, ptEntry]
    split_ifs <;> first | rfl | exact ih _ _

theorem modBlocks_map' {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ) (L : List (Sˣ × ℕ+)),
    modBlocks f a l = some L → L.map (fun b => ((b.1 : S), (b.2 : ℕ))) = mapBlocks f a l
  | [], a, L, h => by
    simp only [modBlocks, Option.some.injEq] at h
    subst h; rfl
  | (t, s) :: l, a, L, h => by
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨L1, hL1, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [List.map_cons, mapBlocks, modBlocks_map' f l (a + s) L1 hL1]
    rfl

theorem mapBlocks_snd' {A B : Type} (f : ℕ → ℕ → A → B) : ∀ (l : List (A × ℕ)) (a : ℕ),
    (mapBlocks f a l).map Prod.snd = l.map Prod.snd
  | [], _ => rfl
  | (t, s) :: l, a => by simp [mapBlocks, mapBlocks_snd' f l (a + s)]

theorem modBlocks_some {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ), (∀ b ∈ l, 0 < b.2) → (∀ b ∈ l, ∀ a' s, IsUnit (f a' s b.1)) →
      ∃ L, modBlocks f a l = some L
  | [], a, _, _ => ⟨[], rfl⟩
  | (t, s) :: l, a, h1, h2 => by
    obtain ⟨L1, hL1⟩ := modBlocks_some f l (a + s) (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
      (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    have hu : IsUnit (f a s t) ∧ 0 < s := ⟨h2 (t, s) List.mem_cons_self a s, h1 (t, s) List.mem_cons_self⟩
    rw [modBlocks, dif_pos hu, hL1]
    exact ⟨_, rfl⟩

end GlobalTheory.LocalBlockEntries

end

open Formalism.L2.SG.Pf.AtPt in
theorem GlobalTheory.LocOver.isPoint_of_scaled : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS), ZhatOM (ZhatL F F') = ptMat w → P.A.f = scaled Z p (frame F) → P.B.f = scaled Z p (frame F') → P.IsPoint := by
  intro D Z p T T' F F' w P hZ hA hB
  let fB : ℕ → ℕ → D.host.E → (D.s.atP p).Ep := fun a s t =>
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Z p)⁻¹ ^ nu D.R.rS a (a + s - 1)) * (D.s.atP p).ιE t
  have hunit : ∀ b ∈ w.1, ∀ a' s, IsUnit (fB a' s b.1) := fun b hb a' s =>
    (Formalism.L2.SG.Pf.BBTie.bt_alg_unit p (pow_ne_zero _ (inv_ne_zero (yP_ne Z p)))).mul
      (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p (w.2.1 b hb).1)
  obtain ⟨L, hL⟩ := GlobalTheory.LocalBlockEntries.modBlocks_some fB w.1 1 (fun b hb => (w.2.1 b hb).2) hunit
  have hLm := GlobalTheory.LocalBlockEntries.modBlocks_map' fB w.1 1 L hL
  have hsize : (L.map (fun b => (b.2 : ℕ))).sum = D.R.rS + 1 := by
    have := congrArg (List.map Prod.snd) hLm
    rw [List.map_map, GlobalTheory.LocalBlockEntries.mapBlocks_snd'] at this
    rw [← w.2.2, ← this]; rfl
  refine ⟨⟨L, hsize⟩, fun a b => ?_⟩
  have hR : (⟨L, hsize⟩ : Formalism.MainNotions.S.Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)).mat a b =
      if b = sgF w a then fB (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) else 0 := by
    simp only [Formalism.MainNotions.S.Loc.Pt.mat]
    rw [GlobalTheory.LocalBlockEntries.ptEntryL_eq', hLm, ptEntry_eq, pSig_map, pTau_map _ _ _ _ (by rw [w.2.2]; exact a.2)]
    simp only [sgF, Fin.ext_iff]
  rw [hR]
  have hZab := congrFun (congrFun hZ a) b
  rw [zhatOM_eq, ptMat_apply'] at hZab
  simp only [Sg, Matrix.mul_diagonal] at hZab
  have hL1 : (locH Z p).Zhat P.A.f P.B.f a b =
      frFac Z.δ p b * (D.s.atP p).cj (frFac Z.δ p a) * (D.s.atP p).ιE (ZhatL F F' a b) := by
    simp only [Formalism.MainNotions.S.Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, hA, hB, GlobalTheory.LocOver.scaled]
    rw [Formalism.L2.SG.Pf.BBTie.formP_bc, Z.hcj p]
    rfl
  rw [hL1, frFac_eq, frFac_eq, cj_alg]
  have key : ∀ (X Y : (D.s.atP p).Ep) (z : D.host.E), (-1 : (D.s.atP p).Ep) ^ (D.R.rS - b.val) * (X * Y * (D.s.atP p).ιE z) =
      X * Y * (D.s.atP p).ιE (z * (-1) ^ (D.R.rS - b.val)) := by
    intro X Y z; rw [map_mul, map_pow, map_neg, map_one]; ring
  rw [key, hZab]
  split_ifs with hb
  · subst hb
    simp only [fB]
    rw [nu_eq, pow_add, map_mul]
    ring
  · rw [map_zero, mul_zero]
end

