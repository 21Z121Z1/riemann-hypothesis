import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0714
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0778
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0679
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0595
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0781
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSubgroupOfLocalComponentsSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowAssemble
open GlobalTheory.RowRep GlobalTheory.RowBaseUniq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem piAt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 :=
  GlobalTheory.FunObj.Comparison₂.cpt_idemSum he

theorem isIdemSum_one {ew : AE D} {w : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt ew w) : IsIdemSum ew {w} :=
  ⟨⟨fun _ => ew, fun _ hx => by rw [Finset.mem_singleton.1 hx]; exact h, by simp⟩, h.1.2.1⟩

theorem suppAt_one {e : AE D} {V : HSp D} : SuppAt e V 1 := fun i j => by
  change (e + cA D e) * (mt V 1 - 1) i j = (mt V 1 - 1) i j
  rw [show mt V (1 : GA D V) = 1 from rfl, sub_self]
  simp

theorem suppAt_mul {e : AE D} {V : HSp D} {g h : GA D V} (hg : SuppAt e V g) (hh : SuppAt e V h) :
    SuppAt e V (g * h) := by
  intro i j
  have e1 : mt V (g * h) - 1 = (mt V g - 1) * (mt V h - 1) + (mt V g - 1) + (mt V h - 1) := by
    rw [show mt V (g * h) = mt V g * mt V h from rfl]
    noncomm_ring
  have s : (e + cA D e) * ((mt V g - 1) * (mt V h - 1)) i j = ((mt V g - 1) * (mt V h - 1)) i j := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hg i k]
  rw [e1, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, s, hg i j, hh i j]

theorem suppAt_of_le {e e' : AE D} {V : HSp D} {g : GA D V}
    (hf : (e' + cA D e') * (e + cA D e) = e' + cA D e') (h : SuppAt e' V g) : SuppAt e V g := fun i j => by
  linear_combination (1 - (e + cA D e)) * h i j + (mt V g - 1) i j * hf

theorem loc_eq_one {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) {u : Pl D.host.E}
    (hu : piAt u (a + cA D a) = 0) : GlobalTheory.StdFrames.loc u (Lev.finE V g) = 1 := by
  refine Units.ext ?_
  change (mt V g).map (piAt u) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Kw u))
  rw [← Matrix.map_one (piAt u) (map_zero _) (map_one _)]
  refine Matrix.ext fun i j => ?_
  have k := congrArg (piAt u) (h i j)
  rw [RingHom.map_mul, hu, zero_mul, Matrix.sub_apply, RingHom.map_sub] at k
  exact sub_eq_zero.1 k.symm

theorem exists_subgroup_elem_localComponents_subset {V : HSp D} {P : Finset (Pl D.host.E)} {e : AE D} (H : Subgroup (GA D V)) (r : GA D V)
    (hw : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1) :
    ∀ Q ⊆ P, ∃ y ∈ H, SuppAt e V y ∧ (∀ u ∈ Q, GlobalTheory.StdFrames.loc u (Lev.finE V y) = GlobalTheory.StdFrames.loc u (Lev.finE V r)) ∧
      ∀ u ∈ P, u ∉ Q → GlobalTheory.StdFrames.loc u (Lev.finE V y) = 1 := by
  classical
  intro Q
  refine Finset.induction_on Q ?_ ?_
  · intro _
    exact ⟨1, H.one_mem, suppAt_one, by simp, fun u _ _ => by rw [map_one, map_one]⟩
  · intro w Q hwQ ih hQ
    obtain ⟨y, hy, sy, ly, oy⟩ := ih ((Finset.subset_insert _ _).trans hQ)
    obtain ⟨h, hh, sh, lh, oh⟩ := hw w (hQ (Finset.mem_insert_self _ _))
    refine ⟨y * h, H.mul_mem hy hh, suppAt_mul sy sh, fun u hu => ?_, fun u hu hn => ?_⟩
    · rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hu with hu | hu
      · rw [hu, oy w (hQ (Finset.mem_insert_self _ _)) hwQ, lh, one_mul]
      · rw [ly u hu, oh u (hQ (Finset.mem_insert_of_mem hu)) (fun h' => hwQ (h' ▸ hu)), mul_one]
    · rw [map_mul, map_mul, oy u hu (fun h' => hn (Finset.mem_insert_of_mem h')),
        oh u hu (fun h' => hn (h' ▸ Finset.mem_insert_self _ _)), one_mul]

theorem mem_of_loc : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (H : Subgroup (GA D V)) (r : GA D V), SuppAt e V r →
    (∀ w ∈ P, ∀ ew : AE D, Formalism.L2.NTheta.IsIdemAt ew w → ∃ h ∈ H, SuppAt ew V h ∧
      GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r)) → r ∈ H := by
  intro D V P e he H r hr hyp
  classical
  obtain ⟨e0, e1, e2⟩ := piAt_idemSum he
  obtain ⟨⟨es, hes, -⟩, hec⟩ := he
  have hce : ∀ u ∈ P, piAt u (cA D e) = 0 := fun u hu => by
    have k := congrArg (piAt u) hec
    rwa [RingHom.map_mul, e1 u hu, one_mul, map_zero] at k
  have key : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1 := by
    intro w hw
    obtain ⟨f0, f1, f2⟩ := piAt_idemSum (isIdemSum_one (hes w hw))
    have a : es w * e = es w := ae_ext (by rw [RingHom.map_mul, f0, zero_mul]) fun Q => by
      change piAt Q (es w * e) = piAt Q (es w)
      rw [RingHom.map_mul]
      by_cases hQ : Q = w
      · rw [hQ, f1 w (Finset.mem_singleton_self _), e1 w hw, one_mul]
      · rw [f2 Q (by simpa using hQ), zero_mul]
    have b : es w * cA D e = 0 := by rw [← a, mul_assoc, hec, mul_zero]
    have c : cA D (es w) * e = 0 := by
      have k := congrArg (cA D) b
      rwa [RingHom.map_mul, cA_cA, map_zero] at k
    have d : cA D (es w) * cA D e = cA D (es w) := by rw [← RingHom.map_mul, a]
    have hf : (es w + cA D (es w)) * (e + cA D e) = es w + cA D (es w) := by linear_combination a + b + c + d
    obtain ⟨h, hH, sh, lh⟩ := hyp w hw (es w) (hes w hw)
    refine ⟨h, hH, suppAt_of_le hf sh, lh, fun u hu hne => loc_eq_one sh ?_⟩
    have k := congrArg (piAt u) d
    rw [RingHom.map_mul, hce u hu, mul_zero] at k
    rw [RingHom.map_add, f2 u (by simpa using hne), ← k, add_zero]
  obtain ⟨y, hy, sy, ly, -⟩ := exists_subgroup_elem_localComponents_subset H r key P subset_rfl
  have k : e • mt V r = e • mt V y := smul_eq_of_loc e0 fun w => by
    by_cases hw : w ∈ P
    · exact .inr (ly w hw).symm
    · exact .inl (e2 w hw)
  have hry : r = y := Subtype.ext (Units.ext (eq_of_halves hr sy k (smul_conj k)))
  rw [hry]
  exact hy

end GlobalTheory.RowAssemble

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QEqColPer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem Q_eq_colPer (hM : M.Is t) : ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj))
    (Φ : (chainFrom G Wl t hM σ j hj vN).Data), (chainFrom G Wl t hM σ j hj vN).IsTheta Φ →
    ∀ (F : Fn G (.grid D.R.m D.R.m)), IsContAut _ F → ∀ (φ : GA D (G.V (.top j)) → ℂ), IsContAut _ φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h : (chainFrom G Wl t hM σ j hj vN).Var),
      (chainFrom G Wl t hM σ j hj vN).Q Φ F φ g h = colPer Wl hM σ j hj vN Φ F φ g h
  | 0, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, _ => LastSeeSawStep.main G Wl t hM j hj vN Φ.1 Φ.2 F φ hΦ.1 hΦ.2 hF hφ g
  | σ + 1, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, h => by
    have ih := Q_eq_colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 hΦ.2.2 F hF
    let B := besAt G hM j (σ + 1) hj vN
    let J := jacAt G hM (j + 1) (σ + 1) (by omega)
    let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
    let s₁ : StepBF Wl.ψ B J :=
      stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
    let s₂ : StepFB Wl.ψ J B' :=
      stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
    have t₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h.1) Φ.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h.1) _ hΦ.1)
    have t₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h.1, h.2.1) Φ.2.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).2 _ J B' s₂ _ (s₂.weil.om_pres (h.1, h.2.1) _ hΦ.2.1)
    have hc := GlobalTheory.FinPl.ValDbl.contAut_hand0 s₁ s₂ (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) hφ t₁ t₂
    have e := ih _ hc h.2.1 h.2.2
    refine e.trans ?_
    show colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2 = colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2
    congr 1
    exact dbl_hand_eq_biLift G Wl t hM σ j hj vN Φ.1 Φ.2.1 φ hΦ.1 hΦ.2.1 hφ g h.1 h.2.1

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem iter_chain (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter ((chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := (GlobalTheory.Unf.unfoldings_of_chain D).2.2.2.2.2.1 Wl.ψ _ _ _ (chain G Wl t hM) (chainData G Wl t hM d) F φ 1
    (chainData_isTheta G Wl t hM d hd) hF hφ hR
  have e : rTrans 1 ((chain G Wl t hM).down (chainData G Wl t hM d) F) = (chain G Wl t hM).down (chainData G Wl t hM d) F := by
    funext z; simp [rTrans]
  rwa [e] at h

theorem chain_Q_eq (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ) (h' : (chain G Wl t hM).Var) :
    (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 h' =
      colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 h' :=
  Q_eq_colPer Wl hM _ 0 top_idx (topVN hM) _ (chainData_isTheta G Wl t hM d hd) F hF φ hφ 1 h'

theorem iter_colPer (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter (colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := iter_chain Wl hM d hd F hF φ hφ hR
  have e : (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 = colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 :=
    funext (chain_Q_eq Wl hM d hd F hF φ hφ)
  rwa [e] at h

end GlobalTheory.RowChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdCharSymplecticRealAdelicPointsModelFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_symplectic_realAdelicPoints_modelForm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D)
    (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis V b → ∀ (r : ℕ) (hr : W.rank = r)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r), ModelW W hr X → ∀ (Xm Ym : Matrix (Fin W.rank) (Fin V.rank) D.host.E),
    ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Xm) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Ym)) =
      Complex.exp (Real.pi * Complex.I * ∑ a, ((Algebra.trace ℚ D.host.E (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
        (fun m => ∑ n, Xm (Fin.cast hr.symm m) n * b n a) (fun m => ∑ n, Ym (Fin.cast hr.symm m) n * b n a)) : ℚ) : ℂ)) := by
  first | exact @GlobalTheory.ArchPhase.psi_symplOH_realPt | exact GlobalTheory.ArchPhase.psi_symplOH_realPt | (intros; apply GlobalTheory.ArchPhase.psi_symplOH_realPt <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaDictionaryLatticeOfFrameCoordinatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDictionary_lattice_of_frameCoordinates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i),
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ v : Fin D.R.r → D.host.E,
      v ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).Λ ↔
        (fun m => v (Fin.cast (rank_Wc i) m)) ∈ latG (Wc D i) (γ * g) := by
  first | exact @GlobalTheory.DictLatPin.lat_of_frAt | exact GlobalTheory.DictLatPin.lat_of_frAt | (intros; apply GlobalTheory.DictLatPin.lat_of_frAt <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOrientedModelEqOfRealAdelicPointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_orientedModel_eq_of_realAdelicPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : WO S T → ℂ),
    IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ →
    (∀ X : Matrix (Fin T.rank) (Fin S.rank) D.host.E, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X) = f₂ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X)) →
    f₁ = f₂ := by
  first | exact @GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | exact GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | (intros; apply GlobalTheory.ThetaUniqReal.eq_of_eq_realPt <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZeroStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ v, vac v ≠ 0) → (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] (p : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] P) (Q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type)
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ i, ∀ v ∉ T, φ i v = vac v) → ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = 0 →
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) = 0 := by
  first | exact @GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | exact GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | (intros; apply GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure <;> assumption)
end

