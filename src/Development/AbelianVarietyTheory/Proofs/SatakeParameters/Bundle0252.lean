import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.GlobDet.main | exact GlobalTheory.GlobDet.main | (intros; apply GlobalTheory.GlobDet.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Fwd

theorem sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V)
    (op : I → Module.End K V) (opC : I → Module.End ℂ W)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (hint : ∀ i x, j (op i x) = opC i (j x)) (hc : Formalism.L2.Col.PairComm opC) (Q : (I → K) → Prop) {u : W}
    (hu : u ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V))) (hu0 : u ≠ 0) {y : I → ℂ}
    (hy : ∀ i, opC i u = y i • u) : ∃ s, Q s ∧ y = fun i => σ (s i) := by
  have h1 := (GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp hint).2.1 Q
  rw [h1] at hu
  by_contra hne
  have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ∃ s, Q s ∧ x = fun i => σ (s i)) (C' := fun x => x = y)
    (fun x hx h => hne (h ▸ hx))
  have hu' : u ∈ Formalism.L2.Col.eigSum opC (fun x => x = y) :=
    Formalism.L2.Col.eigAt_le_eigSum (op := opC) (C := fun x => x = y) rfl (Formalism.L2.Col.mem_eigAt_of_forall_apply hy)
  exact hu0 ((Submodule.disjoint_def.1 hd) u hu hu')

end GlobalTheory.Hk3.Fwd

open GlobalTheory.Hk3.Fwd in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Hk3.passage_of_carried : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos hB hTr j pl cV cW hLD p c hCar hW
  obtain ⟨sy, x, hxg, hxe, hxW, hx0, hlab⟩ :=
    GlobalTheory.T.exists_good_rational_eigenform_hitting_carried_part hHowe R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos j pl cV cW hLD p c hCar hW
  obtain ⟨hCore, hSF, -, -, hEE, hWW, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCar.1
  have hu0 := GlobalTheory.T.upward_theta_lift_injective_on_carried_part R F hB hPos p c hCar w hw hw0
  obtain ⟨hOpsX, hOpsV⟩ := GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models
  obtain ⟨hX, hXo, hXn⟩ := hOpsX A3.A.μ0
  obtain ⟨hV, hVo, -⟩ := hOpsV j A3.A.μ0
  obtain ⟨plX, cX, c0, hRD⟩ := GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hHowe R F hInt hC hEx hSch hJ A3.A.μ0
  have hsplit := GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 core.lev core.fam core.models
  have hM := core.models
  have hBx := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R A3.A.μ0).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX A3.A.μ0
  have hk := kForm_semi (R.jX A3.A.μ0) (R.HX A3.A.μ0).e (R.B.R A3.A.μ0).pres.extL (fun x => hM.jX A3.A.μ0 x) hinj
    (hrange.trans hBx.2.symm) (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hBx.1
  have hjop : ∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = hX (plX i) (cX i) (R.jX A3.A.μ0 f) := hRD.op hX hXo
  have hcomm : Formalism.L2.Col.PairComm (fun i => hX (plX i) (cX i)) := fun a b => hXn.1 _ _ (hRD.good a) (hRD.good b) _ _
  have hwE : w ∈ EEc R.toRealDat R.SF c := hEE c ▸ hw
  have hy : ∀ i, hX (plX i) (cX i) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
      evC (Yc D 0) (plX i) (fun d => c (plX i) (dualLab d)) (c0 i) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i =>
    (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 core hSch R.SF hSF A3.A.μ0 (plX i) (hRD.good i) (cX i) (c0 i) (hRD.mat i) hX hXo).2 c w hwE
  have hu : LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (R.jX A3.A.μ0 ''
      (Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll ((A3.rowI A3.A.μ0).HasRes3 p.1) : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hCar.2 (Submodule.mem_map_of_mem hw)
  obtain ⟨sR, hsR, hyR⟩ := sys_of_mem_span D.what₂.embLL (R.jX A3.A.μ0) (Module.Basis.ofVectorSpace _ _)
    (A3.rowI A3.A.μ0).opAll (fun i => hX (plX i) (cX i)) hk.1 hk.2 hjop hcomm _ hu hu0 hy
  have hXs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ D.sp.X'.rank →
      hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
        D.what₂.embLL (sR (Sum.inl (P, k))) • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P k hkr
    have heq : hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) = hX (plX (Sum.inl (P, k))) (cX (Sum.inl (P, k))) := by
      refine LinearMap.ext_on hk.2 ?_
      rintro _ ⟨b, rfl⟩
      exact ((hsplit.1 A3.A.μ0 hX hXo P k hkr _).symm).trans (hjop (Sum.inl (P, k)) _)
    exact (LinearMap.congr_fun heq _).trans ((hy (Sum.inl (P, k))).trans
      (congrArg (fun z : ℂ => z • LinearMap.adjoint (R.Th A3.A.μ0) w) (congrFun hyR (Sum.inl (P, k)))))
  have hVs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ (Vc D j).rank →
      hV (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (sy (Sum.inl (P, k))) • R.jV j A3.A.μ0 x := by
    intro P k hkr
    have h1 : A3.A.heckeL j A3.A.μ0 (P, k) x = sy (Sum.inl (P, k)) • x := hxe (Sum.inl (P, k))
    exact (hsplit.2 j A3.A.μ0 hV hVo P k hkr x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) h1).trans ((R.jV j A3.A.μ0).map_smulₛₗ _ x))
  have hL := GlobalTheory.T.liftSplitHeckePolys_eq_transfer_residualPolys R.toRealDat F.lv2 hInt core hSch hOk.ok2.irr R.SF hSF j c p.1.1 (fun i => sR (Sum.inl i))
    (fun i => sy (Sum.inl i)) hsR.1 hX hV hXo hVo w hwE hu0 hXs (R.jV j A3.A.μ0 x) (hWW j c ▸ hxW) hx0 hVs
  exact ⟨sy, ⟨hL, hTr j p c hCar sy ⟨x, hxg, hxe, hxW, hx0⟩⟩, hlab⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumpsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_compatibility_of_jumps : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), JumpsCard D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut := by
  first | exact @GlobalTheory.TieGalAssembly.main | exact GlobalTheory.TieGalAssembly.main | (intros; apply GlobalTheory.TieGalAssembly.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.QuadNormRam

theorem not_unrAt_of_ramified : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M],
    Module.finrank K M = 2 → ∀ η : HChar K, IsNormChar M η → ∀ w : HeightOneSpectrum (𝓞 M),
    ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal → ¬ η.UnrAt (w.under (𝓞 K)) := by
  intro F E _ _ _ _ _ h2 η hη w hram hu
  have hGAR : GlobalTheory.Published.GlobalArtinReciprocity := GlobalTheory.globalArtinReciprocity_holds
  obtain ⟨hne, hpow, hsplit⟩ := hη
  rw [h2] at hpow
  let Ω := AlgebraicClosure E
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨artF, haF⟩ := hGAR F Ω
  obtain ⟨artE, haE⟩ := hGAR E Ω
  obtain ⟨δ, hδc, hL⟩ := haF.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) (m := 2) (by norm_num) hpow)
  have hEig : ∀ v : HeightOneSpectrum (𝓞 F), η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := by
    intro v hu A hA
    refine ⟨fun s hs => (hL.unr_iff haF (Or.inr rfl) hA).2 hu s hs, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr haF (Or.inr rfl) hu hA hσ, inv_inv, ι.apply_symm_apply]
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, η.UnrAt (w.under (𝓞 F)) ∧
      ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1 :=
    ((GlobalTheory.QuadNormChar.tendsto_under (K := F) (K' := E)).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))).and hsplit
  have hres : δ.comp (res F Ω E) = 1 := by
    have hS := Filter.eventually_cofinite.1 hev
    refine GlobalTheory.FrobDense.eq_one_of_frob E Ω artE haE (Qbar 2)ˣ _
      (hδc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom F E Ω)) hS.toFinset fun w hw A hA σ hσ => ?_
    have hw' : η.UnrAt (w.under (𝓞 F)) ∧
        ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1 := by
      simpa using hw
    have hf := GlobalTheory.QuadNormChar.normV_under (K := F) w
    have h1 := ((UpperTheory.frobenius_power_compatibility F E Ω 2 ι w _ hf).2 δ _ (hEig _ hw'.1)) A hA
    have h3 := h1.2 σ hσ
    rw [← Units.val_pow_eq_pow_val, hw'.2 _ hf, Units.val_one, map_eq_one_iff _ ι.injective,
      Units.val_eq_one, map_inv, inv_eq_one] at h3
    exact h3

  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  have hAv : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)

  have hmove : ∃ s ∈ Ine (F := F) A, ∃ e : E, s (algebraMap E Ω e) ≠ algebraMap E Ω e := by
    by_contra hfix
    push_neg at hfix
    obtain ⟨hlo, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 F)) w hAv hA hfix
    exact hram (Ideal.ramificationIdx_eq_one_iff.1 he)
  obtain ⟨s, hs, hsm⟩ := hmove
  have hδs : δ s = 1 := (hL.unr_iff haF (Or.inr rfl) hAv).2 hu s hs
  have hδ1 : δ = 1 := MonoidHom.ext fun τ => by
    rcases GlobalTheory.QuadNormChar.fixes_or h2 s hsm τ with ⟨τ', rfl⟩ | ⟨τ', hτ'⟩
    · exact DFunLike.congr_fun hres τ'
    · have := DFunLike.congr_fun hres τ'
      rw [MonoidHom.comp_apply, hτ', map_mul, map_inv, hδs, inv_one, one_mul] at this
      exact this
  apply hne
  apply Subtype.ext
  refine MonoidHom.ext fun x => Units.ext ?_
  obtain ⟨τ, hτ⟩ := toAb_surjective (artF x)
  have := hL x τ hτ.symm
  rw [hδ1, infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
    map_eq_one_iff _ ι.symm.injective] at this
  exact this

end GlobalTheory.QuadNormRam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsExists
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResEx

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem res_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Dec (F := K) A :=
  GlobalTheory.DelEps.WeilRes.mem_Dec_iff.2 fun x => GlobalTheory.DelEps.WeilRes.mem_Dec_iff.1 hσ x

theorem res_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Ine (F := K) A :=
  ⟨res_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

theorem res_mem_Weil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') :
    AlgEquiv.restrictScalarsHom K (σ : G L Ω) ∈ Weil h := by
  obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
  have hQ : normV v' = normV v ^ v'.asIdeal.inertiaDeg (𝓞 K) := by
    rw [GlobalTheory.DelEps.WeilRes.normV_eq_pow (K := K) v', GlobalTheory.DelEps.WeilRes.under_eq h h']
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K) * a, v'.asIdeal.inertiaDeg (𝓞 K) * b, res_mem_Dec hab.1,
    fun x hx => ?_⟩
  have h2 := hab.2 x hx
  rw [hQ, ← pow_mul, ← pow_mul] at h2
  exact h2

def resW (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalarsHom K (σ : G L Ω), res_mem_Weil h h' σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

def resI : Ine (F := L) A →* Ine (F := K) A :=
  ((AlgEquiv.restrictScalarsHom K).comp (Ine (F := L) A).subtype).codRestrict (Ine (F := K) A)
    fun σ => res_mem_Ine σ.2

theorem continuous_resI : Continuous (resI (K := K) (L := L) (Ω := Ω) (A := A)) :=
  ((UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω).comp continuous_subtype_val).subtype_mk _

theorem resW_ineIncl (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (τ : Ine (F := L) A) :
    resW h h' (ineIncl h' τ) = ineIncl h (resI τ) := Subtype.ext rfl

def resRep (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {n : ℕ} (a : WDRep h (Fin n → ℂ)) :
    WDRep h' (Fin n → ℂ) where
  ρ := a.ρ.comp (resW h h')
  N := a.N
  smooth := by
    show IsOpen {τ : Ine (F := L) A | a.ρ (resW h h' (ineIncl h' τ)) = 1}
    simp_rw [resW_ineIncl]
    exact a.smooth.preimage continuous_resI
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have hR := normV_zpow_deg_eq σ (resW h h' σ) (fun z => rfl)
    have hC : ((normV v' : ℕ) : ℂ) ^ deg σ = ((normV v : ℕ) : ℂ) ^ deg (resW h h' σ) := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hR
      push_cast at this
      exact this
    show a.ρ (resW h h' σ) * a.N = _ • (a.N * a.ρ (resW h h' σ))
    rw [hC]
    exact a.comm _

end GlobalTheory.AboveL.ResEx

namespace GlobalTheory.AboveL

end GlobalTheory.AboveL

end
end

