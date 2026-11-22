import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SiegelWeilGramDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0313
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.RightRegProps

open GlobalTheory.RightRegFund in

theorem rightReg_unitary_mul_continuous : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.RatDiscrete.rational_points I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : IsFiniteMeasureOnCompacts (I.muA μf) := by
    unfold AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  exact ⟨GlobalTheory.RightRegFund.map_one hD hfund.1 hr hR, GlobalTheory.RightRegFund.map_mul hD hfund.1 hr hR,
    GlobalTheory.RightRegFund.norm_map hD hfund.1 hr hR, GlobalTheory.RightRegFund.continuous_map hD hfund.1 hr hR⟩

end GlobalTheory.RightRegProps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesEqOfAdaptedIsometryInnerLatticesEq
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.SideEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    frame F (Fin.last D.R.rS) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem xflag_top {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Xflag F D.R.rS = Xsp F := by
  simp only [Xflag, Xsp, FlagG.Xa, FlagG.X]
  congr 1
  have : {i : Fin D.R.rS | i.1 < D.R.rS} = Set.univ := by ext i; simp [i.2]
  rw [this, Set.image_univ]

theorem xflag_mono {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {i j : ℕ} (h : i ≤ j) : Xflag F i ≤ Xflag F j := by
  exact Submodule.span_mono (Set.image_mono fun k (hk : k.1 < i) => (lt_of_lt_of_le hk h : k.1 < j))

theorem xflag_eq_range {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (j : ℕ) :
    Xflag F j = Submodule.span D.host.E (Set.range fun i : {i : Fin D.R.rS // i.1 < j} => F.fl.e i.1) := by
  simp only [Xflag, FlagG.Xa]
  congr 1
  ext x; simp

theorem finrank_xflag_eq {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Fintype.card {i : Fin D.R.rS // i.1 < j} := by
  rw [(LinearEquiv.ofEq _ _ (xflag_eq_range F j)).finrank_eq]
  exact finrank_span_eq_card (F.fl.e_indep.comp (fun i : {i : Fin D.R.rS // i.1 < j} => i.1) Subtype.val_injective)

theorem finrank_xflag {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (G : LFlag (VS D) D.R.rS T') (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Module.finrank D.host.E (Xflag G j) := by
  rw [finrank_xflag_eq, finrank_xflag_eq]

theorem map_xflag_le {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
  simp only [Xflag, FlagG.Xa]
  rw [Submodule.map_span_le]
  rintro _ ⟨i, hi, rfl⟩
  have h1 := hg.2 (Fin.castSucc i)
  rw [frame_castSucc, frame_castSucc] at h1
  have e : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) = (g (F.fl.e i) - G.fl.e i) + G.fl.e i := by
    simp
  rw [e]
  refine add_mem ?_ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hle := xflag_mono G (show (Fin.castSucc i).val ≤ j from le_of_lt hi)
  exact hle h1

theorem map_xflag {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j := by
  haveI : FiniteDimensional D.host.E (Xflag G j) :=
    FiniteDimensional.span_of_finite D.host.E ((Set.toFinite _).image _)
  refine Submodule.eq_of_le_of_finrank_eq (map_xflag_le hg j) ?_
  rw [LinearEquiv.finrank_map_eq]
  exact finrank_xflag F G j

theorem map_xsp {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  rw [← xflag_top, ← xflag_top]; exact map_xflag hg _

theorem adapt_mul {T : D.host.E} {F G H : LFlag (VS D) D.R.rS T} {g g' : GV D} (hg : Adapt g F G)
    (hg' : Adapt g' G H) : Adapt (g' * g) F H := by
  refine ⟨mul_mem hg'.1 hg.1, fun a => ?_⟩
  have e : (g' * g) (frame F a) - frame H a = g' (g (frame F a) - frame G a) + (g' (frame G a) - frame H a) := by
    change g' (g (frame F a)) - frame H a = _
    rw [map_sub]; abel
  rw [e]
  refine add_mem ?_ (hg'.2 a)
  rw [← map_xflag hg' a.val]
  exact Submodule.mem_map_of_mem (hg.2 a)

theorem adapt_inv {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    Adapt g⁻¹ G F := by
  refine ⟨inv_mem hg.1, fun a => ?_⟩
  have hm := map_xflag hg a.val
  have h2 := hg.2 a
  rw [← hm] at h2
  obtain ⟨y, hy, hye⟩ := h2
  have e : g⁻¹ (frame G a) - frame F a = -y := by
    have : g (frame F a - y) = frame G a := by
      rw [map_sub]; simp only [LinearEquiv.coe_coe] at hye; rw [hye]; abel
    rw [← this]
    show g.symm (g (frame F a - y)) - frame F a = -y
    rw [LinearEquiv.symm_apply_apply]; abel
  rw [e]; exact neg_mem hy

theorem z_mem_orth {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : F.fl.z ∈ orth (VS D) (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  simp only [Xsp, FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact F.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem nrat_adapt {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) : Adapt n F F := by
  refine ⟨hn.1, fun a => ?_⟩
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_top]
    exact hn.2.2 _ (z_mem_orth F)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inj (g : GV D) {M N : LV D} (h : Formalism.HermitianLatticesTheory.gmap g M = Formalism.HermitianLatticesTheory.gmap g N) : M = N := by
  have := congrArg (Formalism.HermitianLatticesTheory.gmap g⁻¹) h
  rwa [← gmap_mul, ← gmap_mul, inv_mul_cancel, gmap_one, gmap_one] at this

theorem map_toO (g : GV D) (U : Submodule D.host.E (VS D).V) :
    (toO (VS D) U).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      toO (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext x
  simp only [toO, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply]

theorem map_orth {g : GV D} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (U : Submodule D.host.E (VS D).V) :
    (orth (VS D) U).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) =
      orth (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext y
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩ x ⟨u, hu, rfl⟩
    rw [hg u w]; exact hw u hu
  · intro h
    refine ⟨g.symm y, fun x hx => ?_, by simp⟩
    have := h (g x) ⟨x, hx, rfl⟩
    rw [← hg x (g.symm y)]
    simpa using this

theorem lsub_map {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) (Λ : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap g Λ) G = Formalism.HermitianLatticesTheory.gmap g (Lsub Λ F) := by
  have hinj : Function.Injective ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) :=
    g.injective
  simp only [Lsub, Lrep, Formalism.HermitianLatticesTheory.gmap]
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj, map_toO, map_toO, map_orth hg.1,
    map_xsp hg]

theorem side : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (v : D.what₂.Word) (B : LFlag (VS D) D.R.rS ((Tu D v : ℕ) : D.host.E)) (ψ₀ ψ₁ : GV D) (Λa Λb : LV D), Λa ∈ Y.what₂ v → Λb ∈ Y.what₂ v → Adapt ψ₀ (lf D (X.Fu v)) B → Adapt ψ₁ (lf D (X.Fu v)) B → Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ Λa) B = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ Λb) B → Λb = Λa ∧ ∃ n ∈ NRat (lf D (X.Fu v)), n * (ψ₁⁻¹ * ψ₀) ∈ Aut0 (lf D (X.Fu v)) Λa := by
  intro D X Y v B ψ₀ ψ₁ Λa Λb ha hb A0 A1 hL
  have As : Adapt (ψ₁⁻¹ * ψ₀) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul A0 (adapt_inv A1)
  have hsub : Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₁⁻¹ * ψ₀) Λa) (lf D (X.Fu v)) = Lsub Λb (lf D (X.Fu v)) := by
    apply gmap_inj ψ₁
    rw [← lsub_map A1, ← lsub_map A1, ← gmap_mul, mul_inv_cancel_left]
    exact hL
  obtain ⟨n, hn, hnΛ⟩ := GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu v) Λa Λb (ψ₁⁻¹ * ψ₀) ((Y.rowsOK v).1 Λa ha)
    ((Y.rowsOK v).1 Λb hb) As hsub
  have Ans : Adapt (n * (ψ₁⁻¹ * ψ₀)) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul As (nrat_adapt hn)
  have heq : Λa = Λb := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y v v).2 Λb hb Λa ha _ Ans hnΛ
  exact ⟨heq.symm, n, hn, Ans, hnΛ.trans heq.symm⟩

end GlobalTheory.Unfold.SideEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain MeasureTheory Topology
open HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.SiegelWeilConvCompare

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  let e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ) := Homeomorph.piCongrRight fun _ => e
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext i; exact he (x i) (y i)
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ)
    (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  let e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ)
    (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  let R := Ainf F
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
    { toEquiv := eL.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }
  obtain ⟨k0, eA, hA⟩ := exists_coord_Ainf F
  obtain ⟨k, e1, h1⟩ := exists_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))
  refine ⟨k, e0.trans e1, fun x y => ?_⟩
  show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]

theorem exists_coord_tup (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] (n M : ℕ) :
    ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  exact exists_coord_pi e1 h1 (Fin n)

section Zero

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [Subsingleton V]

end Zero

theorem measure_fundamentalDomain_pos (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ) (hμ : IsHaarH F E σ M J μ)
    (𝓕) (h : IsFDH F E σ M J μ 𝓕) : 0 < μ 𝓕 := by
  haveI : μ.IsHaarMeasure := hμ
  haveI : Countable E := (Module.Free.chooseBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  haveI : Countable (HFin (AF F) σ J) := by
    have : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin; rw [Subgroup.coe_map]; exact (Set.to_countable _).image _
    exact this
  haveI : Countable (HFinIn (AF F) σ J) := by
    have : Function.Injective (fun x : HFinIn (AF F) σ J => (⟨x.1.1, x.2⟩ : HFin (AF F) σ J)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : HFin (AF F) σ J => z.1) hxy))
    exact this.countable
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
    ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
  exact pos_iff_ne_zero.2 (IsFundamentalDomain.measure_ne_zero (NeZero.ne μ) h)

section HermTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensHomeo {κ : Type} [Finite κ] (b : Module.Basis κ F E) : R ⊗[F] E ≃ₜ (κ → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

end HermTop

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelWeilGramDensity in

def SiegelFormulaCc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ), 1 ≤ n → 2 * n < M →
    ∀ (T : Matrix (Fin n) (Fin n) E) (hT : IsHermND σ T),
    ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (b : Module.Basis (Fin 2) F E)
      (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
      (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsProdInfFin Φ Φinf Φf → IsSmoothCc F E Φinf → IsPureFin b Φf Φv →
      AllSome (fun μ : Measure (HA (AF F) σ J) => IsHaarH F E σ M J μ) fun μ =>
      AllSome (fun 𝓕 : Set (HA (AF F) σ J) => IsFDH F E σ M J μ 𝓕) fun 𝓕 =>
      AllSome (fun dX : Measure (Fin n → Fin M → Ainf F ⊗[F] E) =>
          SdW F E σ M J (Ainf F) (psiInf F ψ) n dX) fun dXinf =>
      AllSome (fun dS : Measure (HermR (Ainf F) σ n) =>
          SdHerm F E σ (Ainf F) (psiInf F ψ) n dS) fun dSinf =>
      AllSome (fun dX : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
          ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (dX v)) fun dXv =>
      AllSome (fun dS : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
          ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (dS v)) fun dSv =>
      AllSome (fun g : HermR (Ainf F) σ n → ℂ =>
          IsGramDensity (Ainf F) σ J dXinf dSinf Φinf g) fun ginf =>
      AllSome (fun g : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ =>
          ∀ v, IsGramDensity (Fv F v) σ J (dXv v) (dSv v) (Φv v) (g v)) fun gv =>
        Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT.1)) ∧
        meanC μ 𝓕 (thetaS F E σ M J Φ (gramFibre σ J T)) =
          ginf (hermOf (Ainf F) σ T hT.1) * ∏' v, gv v (hermOf (Fv F v) σ T hT.1)

end GlobalTheory.SiegelWeilConvCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadicalStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_unitaryUnipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → (∃ N : Subgroup I.GA, (N : Set I.GA) = I.NA W) ∧ IsClosed (I.NA W) ∧ (∀ m ∈ I.NA W, ((m.1, 1) : I.GA) ∈ I.NA W ∧ ((1, m.2) : I.GA) ∈ I.NA W) ∧ (∀ U : Set I.Gf, U ∈ nhds (1 : I.Gf) → ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, (γ⁻¹ * m).2 ∈ U) ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, γ⁻¹ * m ∈ Cp := by
  first | exact @GlobalTheory.UnipApprox.strong_approximation | exact GlobalTheory.UnipApprox.strong_approximation | (intros; apply GlobalTheory.UnipApprox.strong_approximation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoTsumOfMonotone
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Filter Topology

namespace GlobalTheory.GaussMean.Limit

theorem tendsto_tsum_of_monotone {ι : Type*} (f : ℕ → ι → ENNReal) (g : ι → ENNReal)
    (hm : ∀ y, Monotone fun k => f k y) (ht : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => ∑' y, f k y) atTop (𝓝 (∑' y, g y)) := by
  letI : MeasurableSpace ι := ⊤
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := (Measure.count : Measure ι)) (f := f) (F := g)
    (fun k => (measurable_from_top).aemeasurable) (ae_of_all _ hm) (ae_of_all _ ht)
  simpa only [lintegral_count] using h

theorem tendsto_lintegral_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (p : ι → α → Prop) (hp : ∀ y, MeasurableSet {x | p y x}) (f : ℕ → ι → α → ENNReal) (g : ι → α → ENNReal)
    (hf : ∀ k y, Measurable (f k y)) (hm : ∀ y x, Monotone fun k => f k y x)
    (ht : ∀ y x, Tendsto (fun k => f k y x) atTop (𝓝 (g y x))) :
    Tendsto (fun k => ∫⁻ x, (∑' y : {y // p y x}, f k y.1 x) ∂μ) atTop
      (𝓝 (∫⁻ x, (∑' y : {y // p y x}, g y.1 x) ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (fun k => Measurable.aemeasurable ?_)
    (ae_of_all _ fun x a b hab => ENNReal.tsum_le_tsum fun y => hm y.1 x hab)
    (ae_of_all _ fun x => tendsto_tsum_of_monotone (fun k (y : {y // p y x}) => f k y.1 x) _
      (fun y => hm y.1 x) fun y => ht y.1 x)
  have e : (fun x => ∑' y : {y // p y x}, f k y.1 x) = fun x => ∑' y, {x | p y x}.indicator (f k y) x := by
    funext x
    exact (tsum_subtype {y | p y x} fun y => f k y x).trans (tsum_congr fun y => rfl)
  rw [e]
  exact Measurable.ennreal_tsum fun y => (hf k y).indicator (hp y)

theorem measurable_coord (I : AutInst) (v : InfinitePlace I.F) (w : Fin I.n → ℂ) :
    Measurable fun x : I.GA => ((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ w := by
  have h0 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
    have e : (fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹) = fun g => uMat g⁻¹ := by
      funext g
      exact (Matrix.coe_units_inv g.1).symm
    rw [e]
    exact h0.comp continuous_inv
  have h2 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => ((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ w :=
    (h1.matrix_mul continuous_const).matrix_mulVec continuous_const
  exact h2.measurable.comp ((measurable_pi_apply v).comp measurable_fst)

theorem siegelMean_of_cc : SiegelMeanCc → SiegelMean := by
  intro H I hn s μf _ _ fund hfund
  obtain ⟨hfin, hH⟩ := H I hn s μf fund hfund
  refine ⟨hfin, ?_⟩
  choose φ D h1 h2 h3 using fun v => GlobalTheory.T.exists_truncated_gaussians_with_densities I.n (I.ε v)
  haveI := countable_V I
  have hs : sgn ℝ s ≠ 0 := by cases s <;> simp [sgn]
  have hL := tendsto_lintegral_tsum ((I.muA μf).restrict fund)
    (fun (y : Fin I.n → I.E) (x : I.GA) => y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s)
    (fun y => mand (measurableSet_mem_lam I y) (MeasurableSet.const _))
    (fun k y x => ENNReal.ofReal (∏ v, φ v k (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun y x => ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun k y => ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun v _ =>
      (h1 v k).1.continuous.measurable.comp (measurable_coord I v _)))
    (fun y x a b hab => ENNReal.ofReal_le_ofReal
      (Finset.prod_le_prod (fun v _ => (h1 v a).2.2.1 _) fun v _ => (h2 v _).1 hab))
    (fun y x => ENNReal.tendsto_ofReal (tendsto_finset_prod _ fun v _ => (h2 v _).2))
  have hR : Tendsto (fun k => I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, D v k (sgn ℝ s))) atTop
      (𝓝 (I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal ((tendsto_finset_prod _ fun v _ => h3 v _ hs).const_mul _)) (Or.inr hfin.ne)
  exact tendsto_nhds_unique hL (hR.congr fun k => (hH (fun v => φ v k) (fun v => D v k) fun v => h1 v k).symm)

end GlobalTheory.GaussMean.Limit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTraceStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.St.G.psiEf_transport_rat | exact GlobalTheory.St.G.psiEf_transport_rat | (intros; apply GlobalTheory.St.G.psiEf_transport_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHostFieldArithmeticConditions : GlobalTheory.TypeAsm.HostC := by
  first | exact @GlobalTheory.TypeAsm.hostC | exact GlobalTheory.TypeAsm.hostC | (intros; apply GlobalTheory.TypeAsm.hostC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularColumnOpsPreserveHaarTuplesHermitiaStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_column_ops_preserve_haar_tuples_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X b => ∑ c, u c b • X c) = μ) ∧ ∀ ν : Measure (HermR (Fv F v) σ a), ν.IsAddHaarMeasure → ∀ φ : HermR (Fv F v) σ a → HermR (Fv F v) σ a, (∀ S, (φ S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u) → ν.map φ = ν := by
  first | exact @GlobalTheory.UnitriTuple.unitri_haar | exact GlobalTheory.UnitriTuple.unitri_haar | (intros; apply GlobalTheory.UnitriTuple.unitri_haar <;> assumption)
end

