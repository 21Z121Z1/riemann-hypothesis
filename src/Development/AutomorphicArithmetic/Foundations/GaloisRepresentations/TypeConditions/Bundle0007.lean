import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0889
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SemisimpleOfFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolCoeffZero
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

def SepW (y : WD h) : Prop := y.tame ∧ ∃ s ∈ Ine (F := E) B, (y.inePol s).Separable

theorem SepW.ncW {y : WD h} (k : SepW y) (ht : thr w y.lpDim = 2) : NcW y := by
  obtain ⟨k1, s, hs, k2⟩ := k
  refine ⟨(WD.tame_iff_inePol y).1 k1, WD.noMonodromy_of_inertia_separable_charpoly E Ω B w h y s hs k2, fun γ hγ hc z hz => ?_⟩
  exfalso
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.tame_mk] at k1
  rw [ht, WD.inePol_of_mem_Ine _ hγ, WD.charPol_mk] at hz
  rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
  let U := End.eigenspace (a.ρ (ineIncl h ⟨γ, hγ⟩)) z
  let K : Subgroup (Ine (F := E) B) :=
    { carrier := {σ | ∃ c : ℂ, ∀ v ∈ U, a.ρ (ineIncl h σ) v = c • v}
      one_mem' := ⟨1, fun v _ => by simp⟩
      mul_mem' := fun {x y} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨d * c, fun v hv => by
        rw [map_mul, map_mul, End.mul_apply, hd v hv, map_smul, hc v hv, smul_smul]⟩
      inv_mem' := fun {x} ⟨c, hc⟩ => ⟨c⁻¹, fun v hv => by
        have e : a.ρ (ineIncl h x⁻¹) (a.ρ (ineIncl h x) v) = v := by
          rw [← End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, End.one_apply]
        rw [hc v hv, map_smul] at e
        by_cases h0 : c = 0
        · rw [h0, zero_smul] at e; rw [← e]; simp
        · rw [← e, smul_smul, inv_mul_cancel₀ h0, one_smul, e]⟩ }
  have hop : IsOpen (K : Set (Ine (F := E) B)) :=
    K.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (IsOpen.mem_nhds a.smooth (by
      show a.ρ (ineIncl h 1) = 1
      rw [map_one, map_one])) fun σ hσ => ⟨1, fun v _ => by
      have : a.ρ (ineIncl h σ) = 1 := hσ
      rw [this]; simp⟩)
  have hK : IsClosed ((K.map (Ine (F := E) B).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine B).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hop)
  have hle : Subgroup.closure (insert γ (Wild E B : Set (G E Ω))) ≤ K.map (Ine (F := E) B).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ⟩, ⟨z, fun v hv => End.mem_eigenspace_iff.1 hv⟩, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, ⟨1, fun v _ => by rw [k1 _ hu]; simp⟩, rfl⟩
  obtain ⟨u, ⟨c, hu⟩, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hc hs)
  obtain rfl : u = ⟨s, hs⟩ := Subtype.ext e
  have h1 : finrank ℂ U = (a.ρ (ineIncl h ⟨γ, hγ⟩)).charpoly.rootMultiplicity z := by
    rw [← LinearMap.finrank_maxGenEigenspace_eq, (a.semisimple _).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
  have h2 : finrank ℂ U ≤ (a.ρ (ineIncl h ⟨s, hs⟩)).charpoly.rootMultiplicity c := by
    rw [← LinearMap.finrank_maxGenEigenspace_eq, (a.semisimple _).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
    exact Submodule.finrank_mono fun v hv => End.mem_eigenspace_iff.2 (hu v hv)
  have h3 := rootMultiplicity_le_one_of_separable k2 c
  omega

theorem SepW.dual {y : WD h} (k : SepW y) : SepW y.lpDual := by
  obtain ⟨k1, s, hs, k2⟩ := k
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.tame_mk] at k1
  refine ⟨?_, s⁻¹, inv_mem hs, ?_⟩
  · rw [WD.lpDual_mk, WD.tame_mk]
    intro σ hσ
    rw [WDRep.dual_ρ, k1 σ⁻¹ (inv_mem hσ)]
    rfl
  · rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
    rw [WD.lpDual_mk, WD.inePol_of_mem_Ine _ (inv_mem hs), WD.charPol_mk, WDRep.dual_ρ, LabDual.charpoly_dualMap]
    convert k2 using 3
    exact Subtype.ext (inv_inv s)

theorem SepW.transport {B' : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E)} {h' : IsPlaceOver B' w'} {n : ℕ}
    (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ B' ↔ c y ∈ B)
    {b' : WDRep h' (Fin n → ℂ)} {b : WDRep h (Fin n → ℂ)}
    (e : ∀ (σ' : Weil h') (σ : Weil h), (∀ z, c ((σ' : G E Ω) z) = (σ : G E Ω) (c z)) → b'.ρ σ' = b.ρ σ)
    (k : SepW (WD.mk b)) : SepW (WD.mk b') := by
  obtain ⟨k1, s, hs, k2⟩ := k
  rw [WD.tame_mk] at k1
  have hc' : ∀ y, y ∈ B ↔ c.symm y ∈ B' := fun y => by rw [hc, c.apply_symm_apply]
  have hs' := ConjTransport.conjG_mem_Ine c.symm τ.symm (ConjTransport.symm_alg c τ hτ) hc' hs
  refine ⟨(WD.tame_mk _).2 fun σ hσ => ?_, _, hs', ?_⟩
  · have hw : ConjTransport.conjG c τ hτ σ ∈ Wild E B := ConjTransport.conjG_mem_wild c τ hτ hc hσ
    rw [e σ (ineIncl h ⟨_, Wild_le_Ine hw⟩) fun z => (ConjTransport.conjG_apply_c c τ hτ _ z).symm]
    exact k1 _ hw
  · rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
    rw [WD.inePol_of_mem_Ine _ hs', WD.charPol_mk, e _ (ineIncl h ⟨s, hs⟩) fun z => c.apply_symm_apply _]
    exact k2
end

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def Sep {w : PlE H} (y : A.LP w) : Prop := Tm N A y ∧ ∃ s ∈ Ine (F := H.E) (N.plOm.1 w), (A.inePol y s).Separable

variable {N A}

theorem tm_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Tm N A y ↔ (T.e w y).tame := by
  rw [WD.tame_iff_inePol]
  refine ⟨fun k σ hσ => ?_, fun k σ hσ hw => ?_⟩
  · rw [← T.inePol w y σ (Wild_le_Ine hσ), T.dim]
    exact k σ (Wild_le_Ine hσ) hσ
  · rw [T.inePol w y σ hσ, ← T.dim]
    exact k σ hw

theorem sep_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Sep N A y ↔ SepW (T.e w y) :=
  and_congr (tm_iff T y) (exists_congr fun s => and_congr_right fun hs => by rw [T.inePol w y s hs])

theorem nc_of_sep (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (ht : thr w (A.lpDim y) = 2) (h : Sep N A y) :
    Nc N A y :=
  (nc_iff T y).2 (((sep_iff T y).1 h).ncW (by rwa [T.dim]))

theorem sep_char (hLP : Formalism.MainNotions.SumRepresentations.At.TieLP N A) {w : PlE H} {y c : A.LP w} (hc : A.lpDim c = 1) (tc : Tm N A c)
    (h0 : ∀ s ∈ Ine (F := H.E) (N.plOm.1 w), (A.inePol c s).coeff 0 ≠ 0) (h : Sep N A y) : Sep N A (A.lpChar y c) := by
  obtain ⟨k1, s, hs, k2⟩ := h
  refine ⟨fun σ hσ hw => ?_, s, hs, ?_⟩
  · have e : A.inePol c σ = X - C 1 := by rw [tc σ hσ hw, hc]; simp
    rw [((hLP w y y c c 0 hc hc).2.2.2.2.2 σ hσ).2 1 e, scaleRoots_one, k1 σ hσ hw, A.lpDim_char _ _ hc]
  · obtain ⟨m1, m2⟩ := inePol_monic hLP c s hs
    rw [hc] at m2
    have e : A.inePol c s = X - C (-(A.inePol c s).coeff 0) := by
      rw [C_neg, sub_neg_eq_add]; exact m1.eq_X_add_C m2
    have hz : -(A.inePol c s).coeff 0 ≠ 0 := neg_ne_zero.2 (h0 s hs)
    rw [((hLP w y y c c 0 hc hc).2.2.2.2.2 s hs).2 _ e]
    obtain ⟨n1, -⟩ := inePol_monic hLP y s hs
    have sp := IsAlgClosed.splits (A.inePol y s)
    refine (nodup_roots_iff_of_splits ((monic_scaleRoots_iff _).2 n1).ne_zero (IsAlgClosed.splits _)).1 ?_
    rw [roots_scaleRoots _ hz.isUnit]
    exact (nodup_roots k2).map (mul_right_injective₀ hz)
end

theorem sep_conj (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
    {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : CGTrue hL D T) {a : ℕ} (π : D.naut.CG a) (hc : D.naut.csd π) {w w' : PlE D.host}
    (hw : IsConjPl D.host w w') (k : Sep D.nd D.naut (D.naut.locG π w)) : Sep D.nd D.naut (D.naut.locG π w') := by
  have := host_isCMField D.host
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hpar : ∀ v, T.e v (D.naut.locG π v) = ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 v) := fun v => by
    rw [C.loc, hmk]
    rfl
  rw [sep_iff T, hpar] at k ⊢
  obtain ⟨γ, hγ⟩ := GlobalTheory.exists_tameGenAt_of_isPlaceOver _ _ _ _ (D.nd.plOm.2 w')
  obtain ⟨γ', ⟨c, hcE, hcA, -⟩, -⟩ := GlobalTheory.conjGen_transport_exists D w' w γ (GlobalTheory.TwistDet.isConjPl_symm hw) hγ
  have hcp : ConjPl (IsCMField.complexConj D.host.E).toRingEquiv w w' :=
    (conjPl_iff_mem _ _ _).2 fun x y e => hw x y (e.trans (host_complexConj D.host _))
  obtain rfl : w' = conjSrc (IsCMField.complexConj D.host.E).toRingEquiv w := eq_conjSrc fun x => by
    simpa using (hcp (IsCMField.complexConj D.host.E x)).symm
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
  rw [ParLaws.locPar_mk hL hσ] at k
  rw [ParLaws.locPar_mk hL (ParLaws.isLocComp_flip hc₀ hσ)]
  let π₁ : IrrRep (GL (Fin a) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose a), fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose a),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose a g⟩) σ.irred⟩
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ a σ.V σ.ρ
    (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top _ a σ.V σ.ρ σ.smooth σ.irred) σ.irred
  have hr := ParLaws.isRec_locRec hL (D.nd.plOm.2 w)
  let cc := (IsCMField.complexConj D.host.E).toRingEquiv
  let i := RingEquiv.ofBijective (conjLoc cc w) ⟨(conjLoc cc w).injective, ParLaws.conjLoc_surjective cc w⟩
  let L := longElt a (w.adicCompletion D.host.E)
  obtain ⟨b', b, h1, h2, -, h4⟩ := hL.2 _ _ _ _ _ _ _ _ _ _ _ _ (ParLaws.isRec_locRec hL (D.nd.plOm.2 (conjSrc cc w))) hr c
    (D.host.conj : D.host.E →+* D.host.E) i (fun z => (hcA z).symm) hcE (conjLoc_spec cc w).1
    (fun x => ((conjLoc_spec cc w).2.1 x).trans (congrArg _ (host_complexConj D.host x))) a
    (ParLaws.toRep ⟨σ.V, σ.ρ.comp (ParLaws.flip (conjLoc cc w) a),
        isSmooth_comp σ.smooth _ (ParLaws.continuous_flip (conjLoc_spec _ w).1),
        ParLaws.isIrreducible_comp σ.irred _ (ParLaws.flip_surjective (ParLaws.conjLoc_surjective _ w))⟩) π₁
    (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.ρ.asGroupHom L)) (fun g v => by
      change σ.ρ L (σ.ρ (invRevT (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) v) =
        σ.ρ (invT a _ (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) (σ.ρ L v)
      have e : ∀ (x y : GL (Fin a) (w.adicCompletion D.host.E)) (u : σ.V), σ.ρ x (σ.ρ y u) = σ.ρ (x * y) u :=
        fun x y u => by rw [map_mul]; rfl
      refine (e _ _ v).trans (Eq.trans ?_ (e _ _ v).symm)
      rw [ParLaws.invRevT_eq, inv_mul_cancel_right])
  obtain ⟨_, _, _, -, H⟩ := hr
  have kd := k.dual
  rw [← H.dual a (ParLaws.toRep σ) π₁ hE, ← h2] at kd
  exact h1 ▸ kd.transport c (D.host.conj : D.host.E ≃+* D.host.E) hcE hcA h4

theorem tm_rankOne (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : CGTrue hL D T)
    {C₀ : CharFrame D} (S : CharSide D C₀) (π : D.naut.CG 1) (w : PlE D.host) (ht : (S.e1 π).1.TameAt w) :
    Tm D.nd D.naut (D.naut.locG π w) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (C.e 1 π)).1 with hχ'
  set χ := (S.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [C.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (S.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := S.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, hf, mul_inv_cancel]
  rw [tm_iff T, hloc, hchar, ParLaws.locPar_ofChar]
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL (D.nd.plOm.2 w)
  rw [H.one]
  refine GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((PositivityTheory.LocalParametersCuspidal.DZC.tame_lpOfChar_iff _ _).2 fun σ hσ => ?_)
  exact GlobalTheory.MuTameQS.isTame_loc ht _ ((GlobalTheory.MuTameQS.val_lt_one_iff w _).2 (PositivityTheory.LocalParametersCuspidal.DZC.wild_to_unitsOne a ha σ hσ))

theorem inePol_coeff_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (c : A.LP w) (s) (hs : s ∈ Ine (F := H.E) (N.plOm.1 w)) :
    (A.inePol c s).coeff 0 ≠ 0 := by
  rw [T.inePol w c s hs, WD.inePol_of_mem_Ine _ hs]
  obtain ⟨n, a, e⟩ := (T.e w c).exists_rep
  rw [← e, WD.charPol_mk]
  intro h0
  have hu : IsUnit (a.ρ (ineIncl (N.plOm.2 w) ⟨s, hs⟩)) := (Group.isUnit _).map a.ρ
  have hd := (LinearMap.isUnit_iff_isUnit_det _).1 hu
  rw [LinearMap.det_eq_sign_charpoly_coeff, h0, mul_zero] at hd
  exact not_isUnit_zero hd

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.NonCriticalLocalParamOfFullDim
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace UpperTheory.GalS

theorem nonCritical_localParam_of_full_dim (D : D7) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (i : D.nd.Loc) (P : D.naut.AV i) (w : PlE D.host) (hw : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i)
    (hA : w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde')))) (hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV) :
    Nc D.nd D.naut (D.naut.locV i P w) := by
  obtain ⟨hχ, hDel⟩ := (GlobalTheory.T.tame_descent_conditions_every_localisation D i).1
  obtain ⟨m, p⟩ := h4.1 i P w hw (hA.imp id fun h => ⟨hDel, h.2⟩)
  refine ⟨fun σ hσ hW => ?_, m, fun γ hγ z hz => ?_⟩
  · have e : chi1 D.nd i σ = 1 := by
      show ((D.nd.chi i 1 σ : (D.nd.O i)ˣ) : D.nd.O i) = 1
      rw [hχ w hA σ hW, Units.val_one]
    rw [p σ hσ, e, map_one, map_one, ← pow_add, hd]; rfl
  · have h1 : (D.naut.inePol (D.naut.locV i P w) γ).IsRoot z := (rootMultiplicity_pos'.1 (lt_of_lt_of_le (thr_pos w) hz)).2
    rw [p γ hγ.1] at h1
    simp only [IsRoot, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_C, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, one_pow]
    · have k := char_pow_ine (D.nd.plOm.2 w) (D.nd.chi i 1) (hχ w hA) γ hγ.1
      rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, ← map_pow]
      show iotaO D.nd D.naut i (((D.nd.chi i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) ^ _) = 1
      rw [← Units.val_pow_eq_pow_val, k, Units.val_one, map_one]

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PowEqOneOfRoots
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
open scoped commutatorElement

namespace UpperTheory.GalS

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem mem_of_gen {n : ℕ} {a : WDRep h (Fin n → ℂ)} (ha : a.Tame) {γ : G E Ω} (hγ : TameGenAt A γ)
    (S : Subgroup (End ℂ (Fin n → ℂ))ˣ) (h1 : a.ρ.toHomUnits (ineIncl h ⟨γ, hγ.1⟩) ∈ S) (σ : Ine (F := E) A) :
    a.ρ.toHomUnits (ineIncl h σ) ∈ S := by
  let K : Subgroup (Ine (F := E) A) := S.comap (a.ρ.toHomUnits.comp (ineIncl h))
  have one : ∀ τ : Ine (F := E) A, a.ρ (ineIncl h τ) = 1 → τ ∈ K := fun τ e => by
    have : a.ρ.toHomUnits (ineIncl h τ) = 1 := Units.ext e
    show a.ρ.toHomUnits (ineIncl h τ) ∈ S
    rw [this]; exact S.one_mem
  have hO : IsOpen (K : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := (a.ρ.comp (ineIncl h)).ker) (fun τ e => one τ e) a.smooth
  have hK : IsClosed ((K.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hO)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ K.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, one _ (ha _ hu), rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem pow_eq_one_of_roots {n : ℕ} {f : End ℂ (Fin n → ℂ)} (hf : f.IsSemisimple) {m : ℕ}
    (k : ∀ z : ℂ, f.charpoly.IsRoot z → z ^ m = 1) : f ^ m = 1 := by
  have top := hf.iSup_eigenspace_eq_top
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ z, f.eigenspace z := top ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem z x hx =>
    by_cases h0 : x = 0
    · simp [h0]
    · have he : f.HasEigenvector z x := ⟨hx, h0⟩
      rw [he.pow_apply, k z ((End.hasEigenvalue_iff_isRoot_charpoly _ _).1 (End.hasEigenvalue_of_hasEigenvector he))]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

theorem tor_of_ncW {y : WD h} (ht : thr w y.lpDim = 1) (k : NcW y) : UpperTheory.GalStar.Tor y := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  have ha : a.Tame := (WD.tame_mk a).1 ((WD.tame_iff_inePol _).2 fun σ hσ => k.1 σ hσ)
  obtain ⟨γ, hγ⟩ : ∃ γ : G E Ω, TameGenAt A γ := GlobalTheory.exists_tameGenAt_of_isPlaceOver E Ω A w h
  let u := a.ρ.toHomUnits
  let g : Weil h := ineIncl h ⟨γ, hγ.1⟩
  have hq : 1 ≤ normV w := Nat.pos_of_ne_zero fun h0 => by
    have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact (Nat.card_pos (α := 𝓞 E ⧸ w.asIdeal)).ne' h0
  have p1 : a.ρ g ^ (normV w - 1) = 1 := pow_eq_one_of_roots (a.semisimple g) fun z hz => by
    refine k.2.2 γ hγ.1 hγ.2 z ?_
    rw [ht, WD.inePol_of_mem_Ine _ hγ.1, WD.charPol_mk]
    exact (rootMultiplicity_pos (LinearMap.charpoly_monic _).ne_zero).2 hz
  have p2 : a.ρ (frob h * g * (frob h)⁻¹) = a.ρ g := by
    rw [ha.conj_eq_pow hγ.1 deg_frob, ← Nat.sub_add_cancel hq, pow_succ, p1, one_mul]
  have c1 : Commute (u (frob h)) (u g) := by
    have e : u (frob h * g * (frob h)⁻¹) = u g := Units.ext p2
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at e
    exact e
  have cen : ∀ x : (End ℂ (Fin n → ℂ))ˣ, Commute x (u g) → ∀ σ, Commute x (u (ineIncl h σ)) := fun x hx σ =>
    Subgroup.mem_centralizer_singleton_iff.1
      (mem_of_gen ha hγ (Subgroup.centralizer {x}) (Subgroup.mem_centralizer_singleton_iff.2 hx.symm) σ) |>.symm
  have c2 := cen _ c1
  have c3 : ∀ τ σ, Commute (u (ineIncl h τ)) (u (ineIncl h σ)) := fun τ => cen _ (cen _ (Commute.refl _) τ).symm
  intro s t
  have c : Commute (u s) (u t) := by
    obtain ⟨τ, e⟩ := exists_eq_zpow_mul deg_frob s
    obtain ⟨τ', e'⟩ := exists_eq_zpow_mul deg_frob t
    rw [e, e', map_mul, map_mul, map_zpow, map_zpow]
    exact Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self _ _ _) ((c2 τ').zpow_left _))
      (Commute.mul_right ((c2 τ).symm.zpow_right _) (c3 τ τ'))
  have e : a.ρ ⁅s, t⁆ = 1 := by
    have := (map_commutatorElement u s t).trans (commutatorElement_eq_one_iff_commute.2 c)
    exact congrArg Units.val this
  show (WD.mk a).charPol _ = _
  rw [WD.charPol_mk, e, LinearMap.charpoly_one, WD.lpDim_mk]

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
section
noncomputable section

namespace UpperTheory.GalS

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (E →+* Qbar l) → Multiset ℤ} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem IsGalU.aw_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : IsGalU π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w) :
    Aw (wdOf h hl ι r) ((ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2)) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  rw [ParLaws.locPar_mk hL hσ h]
  exact H.aw hl (ParLaws.isRec_locRec hL h) hσ

omit [IsCMField E] in
theorem Aw.eq_unr {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) (hy : y.unr) : x = y := k.unr hy

theorem IsGalU.eq_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : IsGalU π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w)
    (hu : (ParLaws.locPar hL (CG.mk π) h).unr) :
    wdOf h hl ι r = (ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) :=
  (H.aw_locPar hL hF hl h).eq_unr ((WD.unr_tw _ _).2 hu)

omit [IsCMField E] in

theorem unr_rec_of_hasSat {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr := by
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := ParLaws.rec_eq_diag hrc (σ := ParLaws.toRep σ) hα
  have e' : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  rw [e', WD.unr_mk]
  exact WDRep.unr_diag _

theorem exists_aw (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : CuspU) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : CG E a)
    (hc : π.IsCsd) (hr : π.IsRegAlg) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        Aw (wdOf h hl ι r) ((ParLaws.locPar hL π h).lpTw ((1 - (a : ℝ)) / 2)) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι ha (π := π) hr hc
  exact ⟨r, Units.continuous_val.comp H.cont, H.ss, fun w hl A h => H.aw_locPar hL hF hl h⟩

theorem nice_of_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (h : IsPlaceOver A w)
    (k : NcW ((ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2))) : Nice π h := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  refine ⟨σ, hσ, _, ParLaws.isRec_locRec hL h, ?_⟩
  rw [rec_algNorm (ParLaws.isRec_locRec hL h) σ]
  rwa [ParLaws.locPar_mk hL hσ h] at k

theorem nice_of_spherical {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (hs : SmGL.IsSpherical σ.ρ) : Nice π h := by
  refine ⟨σ, hσ, rc, hrc, NcW.of_unr ?_⟩
  rw [rec_algNorm hrc, WD.unr_tw]
  exact (ParLaws.unr_iff hrc (ParLaws.toRep σ)).2 hs

end UpperTheory.GalS
end
end

