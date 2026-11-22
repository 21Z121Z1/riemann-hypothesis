import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0130
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.GaugeEx
open GlobalTheory.UnitVectorStabiliser GlobalTheory.HermLineZeros
open scoped TensorProduct Matrix

namespace GlobalTheory.AdelicStabUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_stepData (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    (hJ : IsHermND σ J) (x : Fin 1 → Fin (M + 1) → E) (hx : hE σ J (x 0) (x 0) ≠ 0) :
    ∃ (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      StepData σ J x a B J' := by
  have herm := hf_herm (σ : E →+* E) J (conj_invol h) hJ.1
  obtain ⟨a, ha⟩ := exists_of_fixed h (hE σ J (x 0) (x 0)) (herm _ _)
  let φ := hfLin (σ : E →+* E) J (x 0)
  have hφ : φ ≠ 0 := fun h0 => hx (LinearMap.congr_fun h0 (x 0))
  have hk : Module.finrank E (LinearMap.ker φ) = M := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    rw [Module.finrank_fin_fun] at this
    omega
  let b := Module.finBasisOfFinrankEq E _ hk
  let B : Matrix (Fin (M + 1)) (Fin M) E := Matrix.of fun i j => (b j : Fin (M + 1) → E) i
  have hG : ∀ i j, (Formalism.UG.cT (σ : E →+* E) B * J * B) i j =
      Formalism.UG.hform (σ : E →+* E) J (b i) (b j) := fun i j => by
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  refine ⟨a, B, _, hJ, ?_, ha.symm, fun j => (b j).2, rfl, fun i j => ?_, fun hd => ?_⟩
  · rintro rfl
    exact hx (by rw [← ha, map_zero])
  · rw [hG, hG]
    exact herm _ _
  · obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    let y : LinearMap.ker φ := ∑ j, c j • b j
    have h1 : ∀ i, hfLin (σ : E →+* E) J y (b i) = 0 := fun i => by
      have h2 : hfLin (σ : E →+* E) J (b i) y = 0 := by
        rw [← show _ = (0 : E) from congrFun hc0 i]
        simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Matrix.mulVec,
          dotProduct, hG, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      exact (herm _ _).symm.trans ((congrArg _ h2).trans (map_zero _))
    have h3 : ∀ z : LinearMap.ker φ, hfLin (σ : E →+* E) J y z = 0 := fun z =>
      LinearMap.congr_fun (b.ext (f₁ := hfLin (σ : E →+* E) J y ∘ₗ Submodule.subtype _) (f₂ := 0) h1) z
    have h4 : hfLin (σ : E →+* E) J y (x 0) = 0 :=
      (herm _ _).symm.trans ((congrArg _ (show Formalism.UG.hform _ J (x 0) y = 0 from y.2)).trans (map_zero _))
    obtain ⟨t, p, hp, -⟩ := exists_proj (σ : E →+* E) J (x 0) hx.isUnit (LinearMap.ker φ) fun _ => Iff.rfl
    have h5 : ∀ z, Formalism.UG.hform (σ : E →+* E) J z y = 0 := fun z => by
      have : hfLin (σ : E →+* E) J y z = 0 := by
        rw [hp z, map_add, map_smul, h3, h4, smul_zero, add_zero]
      exact (herm _ _).symm.trans ((congrArg _ this).trans (map_zero _))
    have h6 : J *ᵥ (y : Fin (M + 1) → E) = 0 := funext fun i => by
      have := h5 (Pi.single i 1)
      rw [hf_eq] at this
      simpa [dotProduct, Pi.single_apply, apply_ite] using this
    have h7 : y = 0 := Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h6)
    exact hc (funext (Fintype.linearIndependent_iff.1 b.linearIndependent c h7))

theorem isUnimodularLC_of_equiv {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [MeasurableSpace H]
    (hH : IsUnimodularLC H) (e : G ≃* H) (h1 : Continuous e) (h2 : Continuous e.symm) :
    IsUnimodularLC G := by
  obtain ⟨_, _, _, _, _, -, hH⟩ := hH
  let e' : G ≃ₜ H := ⟨e.toEquiv, h1, h2⟩
  haveI := e'.isEmbedding.t2Space
  haveI := e'.isClosedEmbedding.locallyCompactSpace
  haveI := e'.secondCountableTopology
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ hμ => ⟨fun g => ?_⟩⟩
  haveI := hH _ (MulEquiv.isHaarMeasure_map μ e h1 h2)
  have h3 := congrArg (Measure.map e.symm) (map_mul_right_eq_self (μ.map e) (e g))
  rw [Measure.map_map h2.measurable h1.measurable,
    Measure.map_map (measurable_mul_const _) h1.measurable,
    Measure.map_map h2.measurable ((measurable_mul_const _).comp h1.measurable)] at h3
  convert h3 using 1
  · congr 1
    funext y
    simp
  · rw [show e.symm ∘ e = id from funext fun y => by simp, Measure.map_id]

theorem unimodularOver_of_forall (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R]
    (hR : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ μ : Measure (HA R σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) : UnimodularOver R σ J := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsUnimodularLC (HA R σ J) :=
    fun M J hJ => ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨Measure.haar, inferInstance⟩, hR M J hJ⟩
  refine ⟨key M J hJ, fun x hx => ?_⟩
  cases M with
  | zero => exact absurd (by simp [hE, Formalism.UG.hform]) hx
  | succ M =>
    obtain ⟨a, B, J', hS⟩ := exists_stepData h hJ x hx
    borelize R
    obtain ⟨-, ⟨e, he, -⟩, hc⟩ := GlobalTheory.FrameStep.frameStep F E σ h R M J x a B J' hS
    exact isUnimodularLC_of_equiv (key M J' hS.2.2.2.2.2) e (hc e he).1 (hc e he).2

theorem unimodularOver_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨d, hd⟩ := exists_conj_ne h
  exact unimodularOver_of_forall h (AF F) fun M J hJ μ _ =>
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (conj_invol h) (sub_ne_zero.2 hd)
      (by rw [map_sub, conj_invol h, neg_sub]) hJ μ

end GlobalTheory.AdelicStabUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegralStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPairing_integral_form_row_isIntegral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  first | exact @GlobalTheory.PairAtClass.pair_integral | exact GlobalTheory.PairAtClass.pair_integral | (intros; apply GlobalTheory.PairAtClass.pair_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSubgroupQuotientInvariantMeasure
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureCompact

theorem compactClause : CompactClause := by
  intro G _ _ _ _ _ _ H _ _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  borelize G
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH.isClosed fun h => ?_
  rw [GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact H hH h.2,
    GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact (⊤ : Subgroup H) (by simpa using isCompact_univ)
      (Subgroup.mem_top h)]

end GlobalTheory.QuotientMeasureCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.BarPass

variable {D : D7} {u : D.what₂.Word}

theorem valB_smul_eq {X : Ch D u} {i : ℕ} {M : PtModel X i} (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT)
    (g : M.G) (hg : ∀ v, M.loc v g = 1) (p : M.Pt) : Co.valB w V (g • p) = Co.valB w V p := by
  have h : ∀ v, (g • p).2 v = p.2 v := by
    intro v
    have h1 := M.smul_snd g p v
    rw [hg v] at h1
    apply Subtype.ext
    apply LocF.Raw.ext
    · ext x
      simpa using (h1 x).1
    · funext x
      simpa using (h1 x).2
  unfold PtModel.Coord.valB
  simp only [h]

variable {B : Built.Dat D u} {i : ℕ}

theorem ev_smul (c : D.what₂.LL) (F : B.V i) : B.ev i (c • F) = D.what₂.embLL c • B.ev i F :=
  LinearMap.map_smulₛₗ (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL) c F

theorem isIntegral_torsion {L : Type} [Field L] (ζ : CommGroup.torsion Lˣ) : IsIntegral ℤ ((ζ.1 : Lˣ) : L) := by
  obtain ⟨n, hn, h⟩ := (isOfFinOrder_iff_pow_eq_one).1 ((CommGroup.mem_torsion _).1 ζ.2)
  refine IsIntegral.of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h]
  exact isIntegral_one

theorem act_zeta_mem {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M) {Co : M.Coord}
    (hV : R.ValIs Co) {w : D.what₂.places.Pl} (hw : OverT B.ch w) (b) (d : (B.I.S i).D b) (ζ) (y : M.Val)
    (hy : y ∈ Co.valB w ∅ (R.pt b d)) : M.act (R.zeta ζ) y ∈ Co.valB w ∅ (R.pt b d) := by
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y).1 hy
  refine (hV.dual w hw b d _).2 ⟨((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL) • F, ?_, ?_⟩
  · exact (B.valAt w i _).smul_mem (⟨_, isIntegral_torsion ζ⟩ : 𝓞 D.what₂.LL) hF
  · rw [R.act_zeta, ev_smul, ← hyF]
    rfl

theorem intBar_of_kerBar : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK _ _ hV hV' hb w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  rw [valB_smul_eq Co w ∅ _ (R.loc_zeta ζ)] at hy
  rw [valB_smul_eq Co' w ∅ _ (R'.loc_zeta ζ')]
  have hy0 := act_zeta_mem R hV hw b d ζ⁻¹ y hy
  have hyy : y = M.act (R.zeta ζ) (M.act (R.zeta ζ⁻¹) y) := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  generalize M.act (R.zeta ζ⁻¹) y = y₀ at hy0 hyy
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y₀).1 hy0
  obtain ⟨F', hF', hk⟩ := hb w hw hs b b' d d' F hF
  have hm : B.ev (i + 1) F' ∈ M'.Val := by
    rw [R'.val_eq]
    exact evV_mem_ValC B.emb 1 _ D.what₂.embLL F'
  have h1 : (⟨_, hm⟩ : M'.Val) ∈ Co'.valB w ∅ (R'.pt b' d') := (hV'.dual w hw b' d' _).2 ⟨F', hF', rfl⟩
  refine ⟨_, act_zeta_mem R' hV' hw b' d' ζ' _ h1, ?_⟩
  rw [hyy, K.src, hT, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [hK b b' d d' F y₀ hyF, hk, ev_smul, map_pow, map_natCast]
  rfl

end GlobalTheory.LvT.Built.BarPass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DecoratedLatticePointMoveDiamond
section
noncomputable section

namespace GlobalTheory.LvT.Built

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem levelPrimeDatum_diamond_invariant {E : Type} [Field E] [NumberField E] [StarRing E] (K : Type) [Field K] {n n' : ℕ}
    {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ST SG) (d' : DecoSet E n' ST SG') (P : ST)
    (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) : phiT K (DecoSet.dia1 P a d).1 (DecoSet.dia1 P a d').1 = phiT K d.1 d'.1 := by
  funext x
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun Q => forall_congr' fun y => ?_
  refine imp_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [DecoSet.dia1, DecoSet.dia, Deco.dia]
  exact Units.mul_right_inj _

theorem decoratedLatticePoint_move_diamond {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco = DecoSet.dia1 P a p.1.1.deco ∧
      (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.fr = p.1.1.fr ∧ (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.2 = p.1.2 := by
  have h : p.mv (DecoSet.dia1 P a p.1.1.deco) =
      ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ := dif_pos ⟨p.1.1.2, p.2⟩
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

theorem kAt_dia : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → ∀ b b' d d' (P : Pr.vT u) a, kAt W Ch sel mu cst L A u i b b' ((tdatAt sel mu cst L Tp u i).dia b P a d) ((tdatAt sel mu cst L Tp u (i + 1)).dia b' P a d') = kAt W Ch sel mu cst L A u i b b' d d' := by
  intro X Pr R W Ch sel S mu cst L G m2 u i _ _ _ _ _ Tp A h b b' d d' P a
  obtain ⟨Ξ, -, -, -, -, h⟩ := h b b' d d'
  have key : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p (p.mv (DecoSet.dia1 P a p.1.1.deco)) := by
    intro j p
    obtain ⟨h1, h2, h3⟩ := decoratedLatticePoint_move_diamond p P a
    refine ⟨?_, ?_, h2.symm, h3.symm⟩
    · rw [h1]; exact fun _ _ => rfl
    · rw [h1]; rfl
  have h0 := h d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have h1 := h _ _ (key d) (key d')
  refine h1.trans (Eq.trans ?_ h0.symm)
  rw [(decoratedLatticePoint_move_diamond d P a).1, (decoratedLatticePoint_move_diamond d' P a).1]
  unfold GlobalTheory.KerT.term
  rw [levelPrimeDatum_diamond_invariant]
  rfl

end GlobalTheory.LvT.Built
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section
namespace GlobalTheory.LvT.Built.DilPass

variable {D : D7} {u : D.what₂.Word}

theorem isAct_unique {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n}
    (h₁ : p.IsAct g p₁) (h₂ : p.IsAct g p₂) : p₁ = p₂ := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1]
  · funext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2]

theorem isDil_act {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {a : F}
    {p p' p₁ p₁' : LocF.PP Lc n} (h : LocF.PP.IsDil a p p') (h₁ : p.IsAct g p₁) (h₂ : p'.IsAct g p₁') :
    LocF.PP.IsDil a p₁ p₁' := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  refine ⟨?_, fun x => ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1, h.1]
  · obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2, h.2]

theorem dil_smul {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q : M.Pt} (h : M.Dil v a p q)
    (g : M.G) : M.Dil v a (g • p) (g • q) := by
  refine ⟨M.smul_fst g q p h.1, fun v' hv => ?_, isDil_act h.2.2 (M.smul_snd g p v) (M.smul_snd g q v)⟩
  have h1 := M.smul_snd g q v'
  rw [h.2.1 v' hv] at h1
  exact isAct_unique h1 (M.smul_snd g p v')

theorem dil_unique {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q q' : M.Pt} (h : M.Dil v a p q)
    (h' : M.Dil v a p q') : q = q' := by
  refine Prod.ext (h.1.trans h'.1.symm) (funext fun v' => ?_)
  by_cases hv : v' = v
  · subst hv
    apply Subtype.ext
    apply LocF.Raw.ext
    · rw [h.2.2.1, h'.2.2.1]
    · funext x
      rw [h.2.2.2, h'.2.2.2]
  · rw [h.2.1 v' hv, h'.2.1 v' hv]

theorem dil_pt {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    (v : B.ch.A.vT) (a : (B.ch.A.Fv v)ˣ) (b : (B.I.S i).β) (d : (B.I.S i).D b) :
    M.Dil v a (R.pt b d) (R.pt b ((B.J.A i).dia b (B.pr v) a d)) := by
  have hs : ∀ (P : B.ch.A.vT) (x : Fin (D.R.N i) → (M.Lc P).K), ∃ y : Fin (D.R.N i) → B.E, (fun c => R.iK P (y c)) = x :=
    fun P x => ⟨fun c => (R.iK P).symm (x c), funext fun c => by simp⟩
  have hL : ∀ P, ((R.pt b ((B.J.A i).dia b (B.pr v) a d)).2 P).1.L = ((R.pt b d).2 P).1.L := by
    intro P
    ext x
    obtain ⟨y, rfl⟩ := hs P x
    rw [R.pt_L, R.pt_L, (B.hJ.lev i).dia_N b (B.pr v) a d]
  refine ⟨?_, fun v' hv => ?_, hL v, fun x => ?_⟩
  · have h := (R.fst 1 b ((B.J.A i).dia b (B.pr v) a d) d).2
      ⟨1, map_one _, map_one _, by rw [one_smul]; exact (sp.off b).symm (sp.off_dia b d (B.pr v) a)⟩
    rwa [map_one, one_smul] at h
  · apply Subtype.ext
    apply LocF.Raw.ext (hL v')
    funext x
    obtain ⟨y, rfl⟩ := hs v' x
    exact (R.pt_f _ _ v' y).trans ((congrFun (sp.dia_deco b d (B.pr v) (B.pr v') a hv) y).trans (R.pt_f _ _ v' y).symm)
  · obtain ⟨y, rfl⟩ := hs v x
    refine (R.pt_f _ _ v y).trans (((B.hJ.lev i).dia_f b (B.pr v) a d y).trans ?_)
    rw [← R.pt_f b d v y]
    rfl

theorem ext_ev {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ ψ : M.Val →ₗ[ℂ] V)
    (h : ∀ F (y : M.Val), y.1 = B.ev i F → φ y = ψ y) : φ = ψ := by
  have hsp : M.Val = Submodule.span ℂ (Set.range (B.ev i)) := R.val_eq.trans (span_evV _ _ _ _).symm
  ext ⟨y, hy⟩
  have hy' : y ∈ Submodule.span ℂ (Set.range (B.ev i)) := hsp ▸ hy
  have key : ∀ y ∈ Submodule.span ℂ (Set.range (B.ev i)), ∀ hy : y ∈ M.Val, φ ⟨y, hy⟩ = ψ ⟨y, hy⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨F, rfl⟩ := hz
      exact fun hy => h F _ rfl
    | zero => exact fun hy => (map_zero φ).trans (map_zero ψ).symm
    | add a b ha hb iha ihb =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      have hb' : b ∈ M.Val := hsp ▸ hb
      exact (map_add φ ⟨a, ha'⟩ ⟨b, hb'⟩).trans ((congrArg₂ (· + ·) (iha ha') (ihb hb')).trans (map_add ψ ⟨a, ha'⟩ ⟨b, hb'⟩).symm)
    | smul r a ha iha =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      exact (map_smul φ r ⟨a, ha'⟩).trans ((congrArg (r • ·) (iha ha')).trans (map_smul ψ r ⟨a, ha'⟩).symm)
  exact key y hy' hy

theorem dilLaw_of_kerDil : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  intro D u B i sp sp' M M' R R' k K hT hI hD v a p q p' q' h h'
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  have hq := dil_unique M h (dil_smul M (dil_pt R v a b d) (R.zeta ζ))
  have hq' := dil_unique M' h' (dil_smul M' (dil_pt R' v a b' d') (R'.zeta ζ'))
  have h0 : K.k (R.pt b ((B.J.A i).dia b (B.pr v) a d)) (R'.pt b' ((B.J.A (i + 1)).dia b' (B.pr v) a d')) =
      K.k (R.pt b d) (R'.pt b' d') := by
    refine ext_ev R _ _ fun F y hy => Subtype.ext ?_
    rw [hI _ _ _ _ F y hy, hI _ _ _ _ F y hy, hD b b' d d' (B.pr v) a]
  have hs : ∀ y : M.Val, M.act (R.zeta ζ) (M.act (R.zeta ζ)⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hq, hq']
  refine LinearMap.ext fun y => ?_
  rw [← hs y, K.src, K.src, hT, hT, h0]

end GlobalTheory.LvT.Built.DilPass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilateStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  first | exact @GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | exact GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | (intros; apply GlobalTheory.AdelicCharDilate.exists_eq_std_dilate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnifStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  first | exact @GlobalTheory.SumMaj.summable_majorant | exact GlobalTheory.SumMaj.summable_majorant | (intros; apply GlobalTheory.SumMaj.summable_majorant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntPOfKerP
section
noncomputable section

namespace GlobalTheory.LvT.Built.IntPPass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem ev_smul {D : D7} {u : D.what₂.Word} (B : Built.Dat D u) (i : ℕ) (c : D.what₂.LL) (F : B.V i) :
    B.ev i (c • F) = D.what₂.embLL c • B.ev i F := by
  unfold Built.Dat.ev
  exact map_smulₛₗ _ _ _

theorem intP_of_kerP : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerP k → K.IntP Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK hCo hCo' hV hV' hP w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  set g := R.zeta ζ with hg
  set g' := R'.zeta ζ' with hg'
  have h0 := (GlobalTheory.LvT.ValEq.valB_laws D u B.ch i M Co hCo w hw ∅ (g • R.pt b d)).2.2.2 g⁻¹ y hy
  rw [inv_smul_smul] at h0
  set y₀ := M.act g⁻¹ y with hy₀
  have hyy : y = M.act g y₀ := by
    rw [hy₀, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨F, hF, hFy⟩ := (hV.dual w hw b d y₀).1 h0
  have h1 := hP w hw hs b b' d d' F hF
  have h2 := hK b b' d d' F y₀ hFy
  rw [hT, hyy, K.src, ← map_smul]
  refine (GlobalTheory.LvT.ValEq.valB_laws D u B.ch (i + 1) M' Co' hCo' w hw Finset.univ (R'.pt b' d')).2.2.2 g' _ ?_
  refine (hV'.ker w hw hs b' d' _).2 ⟨_, h1, ?_⟩
  rw [ev_smul, ← h2, map_zpow₀, map_natCast]
  rfl

end GlobalTheory.LvT.Built.IntPPass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVectorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  first | exact @GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | exact GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | (intros; apply GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOneStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_kappa_sq_mul_det_isometry_eq_one : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  first | exact @GlobalTheory.KapVal.norm_kappa_sq_mul_det | exact GlobalTheory.KapVal.norm_kappa_sq_mul_det | (intros; apply GlobalTheory.KapVal.norm_kappa_sq_mul_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeErrorStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primesInProgressions_relativeError : GlobalTheory.Lin.PrimesRel := by
  first | exact @GlobalTheory.Lin.primesRel_holds | exact GlobalTheory.Lin.primesRel_holds | (intros; apply GlobalTheory.Lin.primesRel_holds <;> assumption)
end

