import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotIntertw

open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)

variable {D : D7}

theorem xiN_of_reads {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem isFinPt_one (V : HSp D) {n : ℕ} (e : V.rank = n) :
    GlobalTheory.BotFormula.IsFinPt V 1 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  subst e
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  rw [map_one]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

theorem reads_of_fock {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} (hset : Setup ψ θ S T cc δ r)
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    ∃ G ∈ TT D (tor0 D cc δ) a d, Reads ψ θ hS hT cc δ r G f := by
  obtain ⟨G, hG, hR⟩ := GlobalTheory.VacLine.exists_reads hS hT hset hf hv
  have hRt : ∀ z, Reads ψ θ hS hT cc δ r (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G)
      (wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f) := fun z =>
    (GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hset G f hR z).smul _
  obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hset χS χT om hom 1 1 1 1 (isFinPt_one S hS) (isFinPt_one T hT) f hf 0
  refine ⟨G, ⟨hG, n, hn, fun x hx => ?_⟩, hR⟩
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ hset.crv.1.1 a d 1 1 _ _
    (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d) x hx
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hz
  have hp : n • pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ (n • z) := by
    funext τ i j
    simp [pt, embV, tor0]
    ring
  have h2 := hL (n • z) (fun i j => ⟨_, hz i j, by
    have h0 : (0 : Matrix (Fin d) (Fin a) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    simp⟩)
  have e1 : om (1, 1) = 1 := map_one om
  rw [e1, Module.End.one_apply, Module.End.one_apply] at h2
  have h3 := hRt (n • z)
  have h4 := hRt 0
  rw [GlobalTheory.NormSum.VacMove.pt_zero, GlobalTheory.NormSum.wd_zero] at h4
  rw [GlobalTheory.NormSum.VacMove.pt_zero] at h2
  rw [← h2] at h3
  rw [hp]
  exact GlobalTheory.VacLine.reads_inj hset h3 h4

theorem conj_datum {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (s : T) :
    IsThetaFunO W.ψ A WW (fun w => starRingEnd ℂ (X.f s w)) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ A WW) W.θ τ (cplxO 1 1) (fun w => starRingEnd ℂ (X.f s w)) := by
  have hI := hX.is
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) := (GlobalTheory.ConstRatio.theta_f hI s).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem s)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f s) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst s)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO W.ψ (GlobalTheory.ChiGrid.negSp A) WW (X.f s) from hf), fun τ => ?_⟩
  have h := hv τ
  rw [(hX.std.2.2 τ).1, (hX.stdW.2.2 τ).1] at h
  exact GlobalTheory.BotFormula.ConjJet.isFockVacAt_conj hψ hθ A WW _ hf τ h

theorem bottom_finParts {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    {i j : Fin D.R.m} {s : T} {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪 : Ideal (𝓞 D.host.E)}
    (hB : IsBottom G s i j 𝔪 P P') :
    HasFinPart (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))⁻¹ P.W.chV P.W.ep ∧
    HasFinPart ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
      (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ P.W.chV' (-P.W.ep') := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have h1 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) x y hxy
    have h2 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ hL.eta x y hxy
    have e : (betaH G i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((G.ch.chiH (D.R.m - i)).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) *
          L.C.eta.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) ^ (rankV D i j % 2))⁻¹ := rfl
    rw [hB.chars.1 y, e, MonoidHom.inv_apply, Circle.coe_inv, MonoidHom.mul_apply, MonoidHom.pow_apply, Circle.coe_mul,
      Circle.coe_pow, h1, h2]
    simp
  · have eν : ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
        (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ = G.nu s i (j + 1) := by
      rw [inv_div]; exact mul_div_mul_right_eq_div _ _ _
    have e : (nuH G s i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((nuH G s i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y))⁻¹ := rfl
    rw [eν, zpow_neg, hB.chars.2 y, e, inv_inv]
    exact GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy

theorem bottom_intertwining : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ (r : ℂ) (rc : ℝ), r ≠ 0 ∧ (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
          GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
          ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w))) := by
  intro _ _ _ hInp _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hstd i j A A' WW X δ t0 hX
  by_cases hC : Crv D ⊤ δ
  swap
  · refine ⟨1, 2 * Formalism.L2.Pj.xiR D, one_ne_zero, fun h => absurd h hC, fun τ => ?_, fun s Q P P' _ => absurd P.crv hC⟩
    rw [GlobalTheory.FockPos.norm_embedding_xi0_eq]; simp
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  refine ⟨-δ, (area (lamOf D ⊤ δ))⁻¹, neg_ne_zero.2 hδ, fun _ => rfl, fun τ => ?_, fun s Q P P' hB ea ed => ?_⟩
  · have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq]
    field_simp
  have hSet : Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hstd, W.θ_is, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hw := GlobalTheory.ConjWeilBack.weil_conjRep_of_neg W.ψ A WW _ _ (X.ω s) (hX.is.weil s)
  obtain ⟨hth, hfock⟩ := conj_datum hX s
  obtain ⟨G₀, hG₀, hR₀⟩ := reads_of_fock ea.symm ed.symm hSet hw hth hfock
  obtain ⟨hcS, hcT⟩ := bottom_finParts G hL hB
  have hTT0 : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := GlobalTheory.NormSum.VacMove.vac_TT (hInp D).g1 P.crv P.vac.1
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet _ hTT0
  refine ⟨?_, fun h g x y hg hy => ?_⟩
  · rw [xiN_of_reads W.θ_is _ _ hδ hR₀]; exact hG₀
  · have hv := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw (hInp D) t0 P.pt0
      P.even_mul P.vac hcS hcT x h y g hy hg f₀ hf₀
    have hm := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw P.vac.1 x h y g hy hg 1
      f₀ hf₀ (by rw [one_smul]; exact hv) G₀ hG₀ _ hR₀
    rw [one_smul] at hm
    have e1 : (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
        GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (fun w => starRingEnd ℂ (X.f s w)) := by
      change _ = GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (X.f s))
      rw [GlobalTheory.AdjTr.conjRep_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rfl
    rw [e1, xiN_of_reads W.θ_is _ _ hδ hm, xiN_of_reads W.θ_is _ _ hδ hR₀]

end GlobalTheory.BotIntertw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConstStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_framed_lifts_levelCover_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; ∀ y y' : FrPt Xo c (CAt σ₂), Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y'} := by
  first | exact @GlobalTheory.LevDegree.card_lifts_const | exact GlobalTheory.LevDegree.card_lifts_const | (intros; apply GlobalTheory.LevDegree.card_lifts_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralUniformiserActsByDilationTameKernelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (lattice₂ R i) Ψ → ω (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by
  first | exact @GlobalTheory.BaseCmp.dilKer_of_ne_zero | exact GlobalTheory.BaseCmp.dilKer_of_ne_zero | (intros; apply GlobalTheory.BaseCmp.dilKer_of_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsNsmulOfCommon
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.AmpleTwist

theorem cls_nsmul_of_common {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ)
    (a : Λ) : cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

theorem ampleAt_of_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (A : LB TF.Y.X), A.IsLB → ∀ (ρ χ : AllWt.Weight Dw) (n m : ℕ), IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) → ∀ (y : Y₀ TF.X Z) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), y ∈ nonzeroLocus s → AmpleAt (L₀ TF.X Z (m • χ - ρ)) y := by
  intro E _ _ _ H Dw l Xo c TF Z A hA ρ χ n m hamp y s hs
  have hAg : (A.pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hA _
  have hP : (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n).IsLB := isLB_lbPow hAg n
  have hρ := isLB_L₀ TF.X Z ρ
  have hB : (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)).IsLB := hamp.isLB
  have hN := isLB_L₀ TF.X Z (m • χ - ρ)
  have hN1 := isLB_lbPow hN 1
  have hD := LB.isLB_div hN1 hB
  have hχ := isLB_L₀ TF.X Z χ
  have hχm := isLB_lbPow hχ m
  have hAn := isLB_lbPow hA n
  have hAng : ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hAn _
  have hT := LB.isLB_div hχm hAng
  have hiso : LBIso (LB.div (lbPow (L₀ TF.X Z (m • χ - ρ)) 1)
      (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)))
      (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))) := by
    refine (cls_eq_iff hD hT).1 ?_
    have e := cls_common_add (common₀ TF.X Z) (m • χ - ρ) ρ
    rw [sub_add_cancel] at e
    have e2 := cls_nsmul_of_common (common₀ TF.X Z) m χ
    rw [cls_div hN1 hB hD, cls_div hP hρ hB, cls_lbPow hN 1 hN1, cls_lbPow hAg n hP, cls_pull hA _ hAg,
      cls_div hχm hAng hT, cls_pull hAn _ hAng, cls_lbPow hA n hAn, cls_lbPow hχ m hχm, map_nsmul]
    have e3 : cls (L₀ TF.X Z (m • χ - ρ)) hN = m • cls (L₀ TF.X Z χ) hχ - cls (L₀ TF.X Z ρ) hρ := by
      rw [← e2, e, add_sub_cancel_right]
    rw [e3]
    abel
  obtain ⟨s', hs'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hT hiso s
  refine ⟨1, LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ), s', one_pos, hB, hamp, ?_⟩
  rw [hs']
  exact hs

end GlobalTheory.HSApp.AmpleTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianFieldDataOfToricRatioStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_field_data_of_toric_ratio : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) →
  ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ) (z : D.what₂.LL), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) * p.Tp.psi w) Λ →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    D.what₂.embLL z * Λd s = Λ s →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  first | exact @GlobalTheory.ThmAUpper.val_bound_twisted | exact GlobalTheory.ThmAUpper.val_bound_twisted | (intros; apply GlobalTheory.ThmAUpper.val_bound_twisted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.PureLift GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.GrpTangent
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

theorem eq_epsScale_of_isLieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {c : Fin 1 → R}
    {v : Fin 1 → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb c v w) : w = epsScale (c 0) ≫ v 0 := by
  obtain ⟨u, hu, rfl⟩ := h
  have h1 : (List.ofFn u).prod = u 0 := by simp
  rw [h1]
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact hu 0

theorem push_sub_smul_mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : LieExact A)
    {v : Fin 1 → (epsR R ⟶ A)} (hv : IsLieBasis v) (W : A ⟶ A) [IsMonHom W] {s : Fin 1 → R}
    (e : IsLieComb s v (v 0 ≫ W)) (y : HdR A) : push (dp0 R) (𝟙 _) W y - s 0 • y ∈ Fil A := by
  obtain ⟨u, hu⟩ := (hA.1 y).exists
  obtain ⟨c, hc, -⟩ := hv.2 u hu.1
  have hu' : u = epsScale (c 0) ≫ v 0 := eq_epsScale_of_isLieComb hc
  have hW : v 0 ≫ W = epsScale (s 0) ≫ v 0 := eq_epsScale_of_isLieComb e
  have key : u ≫ W = epsScale (s 0) ≫ u := by
    rw [hu', Category.assoc, hW, epsScale_mul_assoc, epsScale_mul_assoc, mul_comm]
  have h1 := hu.push W
  rw [key] at h1
  exact h1.sub_mem (hu.smul (s 0))

theorem exists_isPolForm (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) :
    ∃ ψ, IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨hall, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨z, hz⟩ : ∃ z, IsChern (dp0 R) (A.hom ≫ 𝟙 (Sp R)) L z :=
    GlobalTheory.Cris.ChernExists.exists_isChern L hL
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hmem : ∀ x, x ∈ prim (dp0 R) (𝟙 (Sp R)) A := fun x => by
    rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hall]
    exact Submodule.mem_top
  refine ⟨_, n, fun k => ⟨a k, hmem _⟩, fun k => ⟨b k, hmem _⟩, ?_, rfl⟩
  have hz' : z = ∑ k, cup _ (a k) (b k) := by
    rw [← e.apply_symm_apply z, ← hab, map_sum]
    exact Finset.sum_congr rfl fun k _ => he _ _
  rw [hz'] at hz
  exact hz

private theorem pGen_pull_refl {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (F : Y ⟶ X) :
    PGen (⟨fun p => (L.pull F).g p.1 p.2⟩ : LB.Iso (L.pull F) (L.pull F)) := by
  intro Z f y j j' k k' h1 h2 h3 h4
  unfold gw
  dsimp only
  have e1 : (f ≫ F) y ∈ L.U j := h1
  have e2 : (f ≫ F) y ∈ L.U j' := h2
  have e3' : F (f y) ∈ L.U (k PUnit.unit) := mem_pull.1 h3
  have e3 : (f ≫ F) y ∈ L.U (k PUnit.unit) := e3'
  have e4' : F (f y) ∈ L.U (k' PUnit.unit) := mem_pull.1 h4
  have e4 : (f ≫ F) y ∈ L.U (k' PUnit.unit) := e4'
  rw [gm_pull_g L F f y (fun _ => j) k (mem_pull.2 h1) h3, gm_pull_g L F f y k k' h3 h4,
    gm_pull_g L F f y (fun _ => j') k' (mem_pull.2 h2) h4]
  have c1 := gm_cocycle hL (f ≫ F) y e1 e2 e4
  have c2 := gm_cocycle hL (f ≫ F) y e1 e4 e3
  have c3 := gm_cocycle hL (f ≫ F) y e3 e4 e3
  have c4 := gm_cocycle hL (f ≫ F) y e3 e3 e3
  have hkk : (gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit))) (L.g (k PUnit.unit) (k PUnit.unit)) = 1 := by
    have h := congrArg (· * ((gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit)))
      (L.g (k PUnit.unit) (k PUnit.unit)))⁻¹) c4
    simpa using h
  have hinv := eq_inv_of_mul_eq_one_right (c3.trans hkk)
  rw [← c2, ← c1, hinv, mul_right_comm]

theorem isPureBC_ell : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω),
    IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  intro hP E _ _ _ H S _ ω C
  unfold IsPureBC
  intro R _ f A _ φ hpb W' _ hW'

  haveI : IsCommMonObj A := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback C.P.isAb hpb
  have hgG : SmoothOfRelativeDimension 1 C.P.A.hom := by
    have h := C.P.smoothDim
    rw [C.dim] at h
    exact h
  have hgA : SmoothOfRelativeDimension 1 A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hpb.1 hgG
  have hLie : LieExact A := (hP.2.1 R A 1 hA hgA).1

  haveI := hgG
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange S R f C.P.A A φ hpb
    (SmoothOfRelativeDimension.smooth 1 C.P.A.hom) 1 ![C.v] C.basis
  have hu : ∀ i, (v' i).left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (![C.v] i).left := hv'φ
  have hw : (v' 0 ≫ W').left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (C.v ≫ C.act.act (GlobalTheory.CM.wK H)).left := by
    rw [Over.comp_left, Category.assoc, hW', ← Category.assoc, hu 0, Over.comp_left, Category.assoc]
    rfl
  have e : IsLieComb (fun i => f (![ω] i)) v' (v' 0 ≫ W') :=
    GlobalTheory.ArcQ.NormalForm.isLieComb_baseChange hpb hu hw C.eig
  have hquot : ∀ y : HdR A, push (dp0 R) (𝟙 _) W' y - f ω • y ∈ Fil A :=
    fun y => push_sub_smul_mem_Fil hLie hv' W' e y

  have hL' : (C.P.L.pull φ).IsLB := pull_isLB C.P.isLB φ
  obtain ⟨ψ, hψ⟩ := exists_isPolForm hP.1 hA hgA hL'
  obtain ⟨hiso, hperf⟩ := hP.2.2.2.2 R A 1 hA hgA (C.P.L.pull φ) hL' ψ hψ
  have hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A (C.P.L.pull φ) :=
    kTriv_pull hpb C.P.isLB hL' (pGen_pull_refl C.P.L C.P.isLB φ) C.P.ktriv
  haveI := hperf hK

  obtain ⟨o', ho'⟩ := GlobalTheory.CM.ellPull_exists_oAct hpb C.act
  haveI := o'.hom (GlobalTheory.CM.wK H)
  haveI := o'.hom (1 - GlobalTheory.CM.wK H)
  have hWo : o'.act (GlobalTheory.CM.wK H) = W' := by
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [ho', hW']
    · rw [Over.w, Over.w]

  have hb : ((1 - GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.bar ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) := by
    rw [show ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.w0 from rfl, GlobalTheory.CM.kform_bar_w0]
    push_cast
    rfl
  have HG : LBIso (cubeLB C.P.A ![fst C.P.A C.P.A ≫ C.act.act (GlobalTheory.CM.wK H), snd C.P.A C.P.A] C.P.L)
      (cubeLB C.P.A ![fst C.P.A C.P.A, snd C.P.A C.P.A ≫ C.act.act (1 - GlobalTheory.CM.wK H)] C.P.L) := by
    have h := C.adj (GlobalTheory.CM.wK H) (1 - GlobalTheory.CM.wK H) hb
    unfold GlobalTheory.CM.LamEq at h
    simpa only [Category.comp_id] using h
  have HA := GlobalTheory.PolAdjoint.lbIso_cube hpb C.P.L hW' (ho' (1 - GlobalTheory.CM.wK H)) HG
  have hadj : ∀ x y : HdR A, ψ (push (dp0 R) (𝟙 _) W' x) y =
      ψ x (push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y) :=
    GlobalTheory.PolAdjoint.adjoint_of_lbIso hP.1 hA hgA hL' hψ W' (o'.act (1 - GlobalTheory.CM.wK H)) HA
  have hpushb : ∀ y : HdR A, push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y = y - push (dp0 R) (𝟙 _) W' y := by
    intro y
    have h1 : GlobalTheory.DeRham.act (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H) = 1 - push (dp0 R) (𝟙 _) W' := by
      rw [map_sub, map_one, GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (GlobalTheory.CM.wK H),
        push_congr (dp0 R) (𝟙 _) hWo]
    rw [← GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H), h1]
    rfl

  have hfil : ∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W' x = f (1 - ω) • x := by
    intro x hx
    have hlie : ∀ y : HdR A, ψ x (push (dp0 R) (𝟙 _) W' y) = f ω * ψ x y := by
      intro y
      have h0 := hiso x hx _ (hquot y)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    have key : ψ (push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x) = 0 := by
      ext y
      rw [LinearMap.map_sub₂, LinearMap.map_smul₂, hadj, hpushb, map_sub, hlie, map_sub, map_one,
        smul_eq_mul, LinearMap.zero_apply]
      ring
    have hinj := (LinearMap.IsPerfPair.bijective_left ψ).1
    have h0 : push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x = 0 := hinj (by rw [key, map_zero])
    exact sub_eq_zero.mp h0
  exact ⟨hfil, hquot⟩

end GlobalTheory.PureLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationEStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compositum_intermediateField_exists_place_valuation_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K] (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F), ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  first | exact @GlobalTheory.UnramCompositum.exists_vLa_eq | exact GlobalTheory.UnramCompositum.exists_vLa_eq | (intros; apply GlobalTheory.UnramCompositum.exists_vLa_eq <;> assumption)
end

