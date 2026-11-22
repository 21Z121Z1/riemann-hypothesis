import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmbExOfRx
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV Formalism.L2.Rows

theorem majAt_frm {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : PosAt H v) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (frm H) v x y = hAt H v x y := by
  have hp := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H v h
  rw [majAt_eq, frm_of_posDef H v hp, (frameOfSpec _ _ hp).2]
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

section Level

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rNab_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) :
    rNab D A P ψ t2 = (rNab D A P ψ t1).map ((rdx h).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  subst e
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, rdx_refl]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩

theorem majAt_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) (v : InfinitePlace D.what₂.LL)
    (hp : PosAt (rH D A P ψ t1) v) (x y : Fin (rDim D A P ψ t1) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (frm (rH D A P ψ t2)) v (rdx h x) (rdx h y) =
      hAt (rH D A P ψ t1) v x y := by
  subst e
  have := D.tcLL
  rw [rdx_refl, rdx_refl]
  exact majAt_frm _ v hp x y

end Level

theorem tie_level (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (tp : D.what₂.Tup → T)
    (j : ∀ μ, (Fin (rDim D A P ψ (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb μ)
    (E : ∀ μ, Matrix (Fin (rDim D A P ψ (tp μ))) (Fin (rDim D A P ψ (tp μ))) D.what₂.LL)
    (op : ∀ μ, S.Amb μ →ₗ[ℂ] S.Amb μ)
    (hF : ∀ μ, FormsTie D.what₂.embLL (j μ) (rH D A P ψ (tp μ)) (E μ) (op μ))
    (hL : ∀ μ, OLatTie D.what₂.embLL (S.Mtilde μ) (j μ) (rNab D A P ψ (tp μ)))
    (f : T' → T) (μ0' : T') (tup : T' → D.what₂.Tup) (hf : ∀ s, f s = tp (tup s))
    (j' : ∀ s, (Fin (rDim D (A.comap f μ0') P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb (tup s))
    (hs : ∀ s, SameOn (j (tup s)) (j' s)) :
    ∃ (Fm : AmbForm D S) (J : AmbIds D (A.comap f μ0') S Fm P ψ tup), AmbTie D (A.comap f μ0') S Fm P ψ tup j' J := by
  have := D.tcLL
  let Fm : AmbForm D S :=
    { MtH := fun μ => toHLat (frm (rH D A P ψ (tp μ))) (rNab D A P ψ (tp μ))
      jAmb := j
      MtH_good := fun μ _ => ⟨frm_det _, GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear D.what₂.embLL (S.Mtilde μ) (j μ) _ (hF μ).li (hL μ)⟩
      jAmb_basis := fun μ _ => by
        show LinearIndependent ℂ (fun i => j μ (Pi.basisFun D.what₂.LL _ i)) ∧
          Submodule.span ℂ (Set.range (fun i => j μ (Pi.basisFun D.what₂.LL _ i))) = ⊤
        simp only [Pi.basisFun_apply]
        exact ⟨(hF μ).li, (hF μ).span⟩
      jAmb_lat := fun μ _ x => (hL μ).2 x
      jAmb_gen := fun μ _ => (hL μ).1
      jAmb_norm := fun μ _ x => GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm D.what₂.embLL D.starLL_cx (j μ) _ _ _ (hF μ) x }
  let J : AmbIds D (A.comap f μ0') S Fm P ψ tup := ⟨fun s _ => rdx (hs s).1⟩
  refine ⟨Fm, J, ⟨fun s _ x => ?_, fun s _ => ?_, fun s _ v hv x y => ?_⟩⟩
  · refine (hs s).2 _ x fun a a' e => ?_
    show x (Fin.cast (hs s).1 a) = x a'
    congr 1
    exact Fin.ext e
  · exact rNab_rdx D A P ψ (hf s) _
  · exact majAt_rdx D A P ψ (hf s) _ v hv x y

set_option maxHeartbeats 3000000 in

theorem ambEx_of_rx : ∀ 𝒮 : Slots, 𝒮.Rx = RX → AmbEx 𝒮 := by
  rintro ⟨Rx, Nx, Sx, Ox⟩ h
  dsimp only at h
  subst h
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro Z l
  have x : RXs l.what₂ := l.rx
  have hsub : R3.tuOf w.I (R3.usedOf w.I T l.Wt) ⊆ R3.tuOf w.I Set.univ := fun τ hτ => by
    obtain ⟨a, -, e⟩ := (R3.mem_tuOf w.I).1 hτ
    exact (R3.mem_tuOf w.I).2 ⟨a, Set.mem_univ _, e⟩
  have hf : ∀ s, TupF.incl hsub s = tAll w.I (l.what₂.r.Y.tup s) := fun s => by
    apply Subtype.ext
    show s.1 = w.I.tup (l.what₂.r.Y.tup s)
    have e : l.what₂.r.Y.tup s = R3.ixOf w.I _ s := l.what₂.r.tup_ix s
    rw [e, R3.tup_ixOf]
  obtain ⟨a, J, hJ⟩ := tie_level (w.st Z).toD7 (RowSide.sharp _) (famAll l.what₂) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I)
    x.all.jA _ _ x.all.formsA x.all.latA (TupF.incl hsub) (mu0F _) l.what₂.r.Y.tup hf l.what₂.r.Y.jA x.jA_use
  obtain ⟨a0, J0, hJ0⟩ := tie_level (w.st Z).toD7 l.p0.s (famAll l.what₂) (R3.lev0 w.I) (R3.chr0 w.I) (tAll w.I)
    x.all.jA0 _ _ x.all.formsAtBottomLevel x.all.latA0 (TupF.incl hsub) (mu0F _) l.what₂.r.Y.tup hf l.what₂.r.Y.jA0 x.movedReadingSameMaps_baseReading_agrees
  exact ⟨a, a0, ⟨J, hJ⟩, ⟨J0, hJ0⟩⟩

end GlobalTheory.AmbCrd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseRowCountEqFinrankTypePartBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.BaseRowCount

theorem sum_finrank_le_of_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    ∑ i, Module.finrank K (S i) ≤ Module.finrank K V := by
  classical
  have h : Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
    exact Module.finrank_directSum (R := K) (fun i => S i)
  rw [← h]
  exact Submodule.finrank_le _

set_option maxHeartbeats 2000000 in

theorem nRows0_eq_finrank_isotE : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ π : D.what₂.FT, D.what₂.nRows0 π = Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHost
  classical
  have hI : Inputs D := GlobalTheory.LinksInputs.inputs_of_hypotheses hW hDS hHC hCR D
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 false)) h0.1.1 h0.2
  have hO := (GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) Y.PY Y.hF (R.βY 0)
    (R.dat0 (R.toRealDat.levR F.lv2 false)) R.e0 _ R.fd0 hI (D.sp.Y_sig _) hB.models.inf Y.stdPsi.1 hs.1 hs.2
    (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)).2
  have hT := Y.tied.base
  let f : D.what₂.EE0 →ₗ[ℂ] _ := (Submodule.subtype _) ∘ₗ Y.Iz.jE.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp Y.Iz.jE.injective
  let Wp : D.what₂.FT → Submodule ℂ D.what₂.EE0 := fun π => (Y.Iz.prt π).comap f

  have hOrth : ∀ π π', π ≠ π' → ∀ x ∈ Wp π, ∀ y ∈ Wp π', ⟪x, y⟫_ℂ = 0 := by
    intro π π' hne x hx y hy
    have hx' : f x ∈ Y.Iz.prt π := hx
    have hy' : f y ∈ Y.Iz.prt π' := hy
    rw [Y.prtE0] at hx' hy'
    obtain ⟨a, ha, hax⟩ := hx'
    obtain ⟨b, hb, hby⟩ := hy'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π))).Iso
        (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π'))) :=
      principalLevelFrame.not_iso_conjT fun h => hne (Y.eFT.injective (principalLevelFrame.rowRepR_inj R.θ _ _ h))
    have key := hO _ _ hni a ha b hb
    rw [hT.ee x y]
    unfold ChainReal.ipE ipMT
    refine Eq.trans ?_ key
    have e1 : ((Y.Iz.jE x : _) : _) = f x := rfl
    have e2 : ((Y.Iz.jE y : _) : _) = f y := rfl
    rw [e1, e2, ← hax, ← hby]
    congr 1
    · exact LinearEquiv.symm_apply_apply _ a
    · exact LinearEquiv.symm_apply_apply _ b
  have hInd : iSupIndep Wp := by
    apply OrthogonalFamily.independent
    rw [orthogonalFamily_iff_pairwise]
    intro σ σ' hne
    rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
    exact hOrth σ σ' hne
  have hle : ∀ π, D.what₂.nRows0 π ≤ Module.finrank ℂ (Wp π) := by
    intro π
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    let v : {σ // D.what₂.ft0 σ = π} → Wp π := fun σ => ⟨D.what₂.onb0 σ.1, by
      show f _ ∈ Y.Iz.prt π
      have := hT.ft σ.1
      rw [σ.2] at this
      exact this⟩
    have hli : LinearIndependent ℂ v := by
      apply LinearIndependent.of_comp (Wp π).subtype
      exact D.what₂.onb0.toBasis.linearIndependent.comp _ Subtype.val_injective
    exact hli.fintype_card_le_finrank
  have hdim : Module.finrank ℂ D.what₂.EE0 = D.what₂.D0 := by
    rw [Module.finrank_eq_card_basis D.what₂.onb0.toBasis, Fintype.card_fin]
  have hsum : ∑ π, D.what₂.nRows0 π = D.what₂.D0 := by
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  have hsle : ∑ π, Module.finrank ℂ (Wp π) ≤ D.what₂.D0 := hdim ▸ sum_finrank_le_of_indep Wp hInd
  have heq : ∀ π, D.what₂.nRows0 π = Module.finrank ℂ (Wp π) := by
    have h2 : ∑ π, D.what₂.nRows0 π = ∑ π, Module.finrank ℂ (Wp π) :=
      le_antisymm (Finset.sum_le_sum fun π _ => hle π) (hsle.trans hsum.ge)
    intro π
    exact (Finset.sum_eq_sum_iff_of_le (fun π _ => hle π)).1 h2 π (Finset.mem_univ π)
  intro π
  rw [heq π]
  have hrng : Y.Iz.prt π ≤ LinearMap.range f := by
    intro z hz
    rw [Y.prtE0] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hz : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap a ∈
        (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc false :=
      ⟨a, (Submodule.mem_inf.1 ha).1, rfl⟩
    refine ⟨Y.Iz.jE.symm ⟨_, hz⟩, ?_⟩
    change (Submodule.subtype _ (Y.Iz.jE (Y.Iz.jE.symm ⟨_, hz⟩))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hmap : (Wp π).map f = Y.Iz.prt π := by
    show ((Y.Iz.prt π).comap f).map f = _
    rw [Submodule.map_comap_eq, inf_eq_right.2 hrng]
  rw [(Submodule.equivMapOfInjective f hf (Wp π)).finrank_eq, hmap, Y.prtE0]
  first
    | exact LinearEquiv.finrank_map_eq _ _
    | exact LinearEquiv.finrank_map_eq (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) _
    | exact ((Submodule.equivMapOfInjective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap (LinearEquiv.injective _) _).finrank_eq).symm

end GlobalTheory.BaseRowCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupContainsPrincipalCongruence
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevQ

theorem princ_in_chart_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a b T f : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E)
    (hG : G.reindex (finCongr h) (finCongr h) = 1) {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ (G.reindex (finCongr h) (finCongr h)) T f bad) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin a → E)) (hfg : Module.Finite (𝓞 E) (reL h Λ))
    (hsp : Submodule.span E (reL h Λ : Set (Fin b → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : GL (Fin a) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ G v Λ →
      (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ,
        (x : Matrix (Fin a) (Fin a) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (n : E ⊗[F] v.adicCompletion F) • z) →
      x ∈ (S.Uloc v).comap (reGL h (E ⊗[F] v.adicCompletion F)).toMonoidHom := by
  subst h
  have hR : ∀ (L : Submodule (𝓞 E) (Fin a → E)), reL rfl L = L := by
    intro L
    ext x
    simp [reL, reV]
  have hGr : G.reindex (finCongr rfl) (finCongr rfl) = G := by
    ext i j; simp
  rw [hR] at hfg hsp
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ_loc_step σ S v hG
  obtain ⟨d, hd, hdA⟩ := GlobalTheory.PrincLat.princ_lat v Λ (Module.Finite.iff_fg.1 hfg) hsp
  refine ⟨M * d, Nat.mul_pos hM hd, fun x hx hpr => ?_⟩
  have hxe : reGL rfl (E ⊗[F] v.adicCompletion F) x = x := by
    apply Units.ext
    ext i j
    simp [reGL]
  show reGL rfl (E ⊗[F] v.adicCompletion F) x ∈ S.Uloc v
  rw [hxe]
  refine hMU x ?_ (hdA M _ hpr)
  have hu : x ∈ UPts σ G (v.adicCompletion F) := hx.1
  rw [hGr]
  exact hu

theorem chart_contains_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hUloc hchi Lb0 hLb β v hv
  have hG := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  have hfg : Module.Finite (𝓞 (I.rec7 l Z).host.E) (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0) := by
    rw [← hLb]; exact (F u).levJ.Lb_fin
  have hsp : Submodule.span (I.rec7 l Z).host.E
      (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 : Set (Fin ((I.rec7 l Z).R.N (B.R.m - 1)) → (I.rec7 l Z).host.E)) = ⊤ := by
    rw [← hLb]; exact (F u).levJ.Lb_span
  obtain ⟨n, hn, hN⟩ := princ_in_chart_gen (sigD (I.rec7 l Z)) (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _))
    ((I.rec7 l Z).sp.X (B.R.m - 1)).gram hG (K β).lev v Lb0 hfg hsp
  exact ⟨n, hn, fun x hx => hN x hx.1 hx.2⟩

end GlobalTheory.Mem.Col2.AdT.LevQ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.FrameMove

open GlobalTheory.Mem.Col2.LevFun GlobalTheory.Mem.Col2.Splice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_mul_ratA_apply {n : ℕ} (g : GL (Fin n) (AfE F E)) (γ : GL (Fin n) E) (r s : Fin n) :
    ((g⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s =
      pullV g (fun t => (γ : Matrix (Fin n) (Fin n) E) t s) r := by
  unfold pullV
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem val_sub_lt_of_liftFr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG) (r s : Fin n) :
    Valued.v (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r) -
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) r s) < 1 := by
  classical
  have hL := GlobalTheory.TopStep.liftFr_spec p.deco.2 w
  have hs := single_mem_stdAt (E := E) (n := n) w.1 s
  have hx : p.deco.1.liftFr w (Pi.single s 1) ∈ p.deco.1.at w.1 := (hL.1 _).2 hs
  obtain ⟨t, ht, htx⟩ := (mem_locP _ _ _).1 hx
  have h1 := h.be w _ htx r
  rw [p.deco.2.be_smul w t _ hx, hL.2 _ hs, redV_single, adAt_pullV_osmul] at h1
  have h2 : HasRes w.1 (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r))
      (Ideal.Quotient.mk w.1.asIdeal (if r = s then 1 else 0)) := by
    refine hasRes_of_mul ht ?_
    convert h1 using 1
    by_cases e : r = s
    · subst e; simp
    · simp [e]
  have h3 := hasRes_sub_lt h2
  convert h3 using 3
  by_cases e : r = s
  · subst e; simp
  · simp [e, Matrix.one_apply]

theorem val_mul_sub_one_le {P : HeightOneSpectrum (𝓞 E)} {n N : ℕ} {A B : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (hA : ∀ r s, Valued.v (A r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s, Valued.v (B r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    Valued.v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  first
  | exact @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | (apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le ..)

theorem le_exp_neg_one_of_lt_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with h0 | h0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem seamGL_apply {D : D7} {Xf : Fields} (sd : Seam D Xf) {n : ℕ} (f : Sp Xf.E n ≃ₗ[Xf.E] Sp Xf.E n) (t s : Fin n) :
    ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) t s = sd.iE (f (Pi.single s 1) t) := by
  have h : ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' f.toLinearMap).map (sd.iE : Xf.E →+* D.host.E) := rfl
  rw [h, Matrix.map_apply, LinearMap.toMatrix'_apply]
  rfl

theorem adAt_pullV_fr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (r s : Fin n) :
    adAt F P.1 (pullV g (p.fr P (Pi.single s 1)) r) = (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion E)) r s := by
  have e1 : GlobalTheory.Mem.ColAd.locM P.1 (g⁻¹ * g) = 1 := by rw [inv_mul_cancel, GlobalTheory.Mem.ColAd.locM_one]
  rw [← e1, GlobalTheory.Mem.ColAd.locM_mul, Matrix.mul_apply]
  unfold pullV
  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, adAt_inclE, ← h.fr P t s]
  rfl

theorem frame_near : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ P : SBof I a, GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (((K (chOf c)).y ⟨c, rfl⟩).1 * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)) := by
  classical
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P
  have hpt := hR.pt c
  have hd := fun z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) ((I.cst a).D P) P z).2.2
  unfold GlobalTheory.TwU.NearAt
  rw [hd]
  have hfb2 := (hd _).1 (hfb P).2
  have e : ∀ {G : Type} [Group G] (y k A C : G), (y * A)⁻¹ * C = (A⁻¹ * k) * ((y * k)⁻¹ * C) := by
    intros; group
  have key := e (G := GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) ((K (chOf c)).y ⟨c, rfl⟩).1
    (k (chOf c)) (GlobalTheory.TwU.ratA _ (fb P))
    (GlobalTheory.TwU.ratA _ (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)))
  rw [key]
  intro r s
  show Valued.v (GlobalTheory.Mem.ColAd.locM P.1 (_ * _) r s - _) ≤ _
  erw [GlobalTheory.Mem.ColAd.locM_mul]
  refine val_mul_sub_one_le hfb2 ?_ r s
  clear r s
  intro r s
  show Valued.v (adAt B.host.F P.1 (_) - _) ≤ _
  rw [inv_mul_ratA_apply]
  have hfr := frsF_eq_ptFr I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P
  have hcol : (fun t => ((GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P) :
      GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) :
        Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) t s) =
      ptFr ((I.stp u a i).rep c).1.1 P.1 (Pi.single s 1) :=
    funext fun t => by rw [seamGL_apply]; exact congrArg (fun f => f (Pi.single s 1) t) hfr
  rw [hcol]
  by_cases hG : P.1 ∈ (B.primes X).vGs
  · rw [(hOk.idx_ok a).depthG P hG]
    have e2 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).deco.1.liftFr ⟨P.1, hG⟩ := by
      unfold ptFr
      rw [dif_pos hG]
      rfl
    rw [e2]
    exact le_exp_neg_one_of_lt_one' (val_sub_lt_of_liftFr hpt ⟨P.1, hG⟩ r s)
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hG
    have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
    have e3 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).fr ⟨P.1, hSQ⟩ := rfl
    have h0 := adAt_pullV_fr hpt ⟨P.1, hSQ⟩ r s
    rw [e3]
    erw [h0, sub_self, map_zero]
    exact zero_le'

end GlobalTheory.Mem.Col2.AdT.FrameMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

theorem deco_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  intro X px I hX U L eG hI hV hL hG t q
  have hz := unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori X I hI L hL t q
  have hu := GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup X px I U L eG hI hL hG t q hz
  refine ⟨⟨_, hu⟩, fun h => ?_, GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter X px I U L eG hI hV hL hG t q hz hu⟩
  refine (decoAd_mul X I hI t h _ hz).trans ?_
  refine congrArg (fun a : Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) =>
    ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)), a) • RowAd.decoAd X I t h) ?_
  exact (mul_inv_cancel_right _ _).symm

end GlobalTheory.Mem.R3.RowDeco
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeClassLocalizationEqUnimodularCompanioStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_class_localization_eq_unimodularCompanion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Y : DivX (I.rec7 l Z)) (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (j : ℕ), j ≤ B.R.m → ∀ (c : (I.stp u μ j).Cl), Submodule.IsLattice B.fields.E ((I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ∧ ∀ x : Fin (B.R.N j) → B.fields.E, (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ↔ (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ ((I.stp u μ j).rep c).1.1.deco.1.N) := by
  first | exact @GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq | exact GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq | (intros; apply GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_chart_from_adelic_dictionary : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E hc.sig J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (e : ℕ) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (k t : GL (Fin n) (AfE F E)) (C : Type) (s : C → DecoF E n ST SG Q) (y : C → GL (Fin n) (AfE F E)) (stab : C → Type) [∀ c, Group (stab c)] (lat : C → Submodule (𝓞 E) (Fin n → E)) (gm : ∀ c, stab c →* UF E n) (ψ : topU S.U t Θ d →* ℂˣ), J = 1 → (∀ v, v ∈ Qv ↔ ∃ P ∈ Q, P.under (𝓞 F) = v) → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → (∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) → k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ S.U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → (∀ c, IsPtOf hc (y c * (k * t)) (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = p) → (∀ c, lat c = (s c).deco.1.L) → (∀ c, Function.Injective (gm c)) → (∀ c (γ : UF E n), γ ∈ (gm c).range ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = s c) → (∀ x : topU S.U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → ψ x = 1) → ∃ C' : ClsG hc.sig J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) stab lat, C'.lev.Lb = S.Lb ∧ C'.lev.U = topU S.U t Θ d ∧ (∀ v, v ∉ Qv → C'.lev.Uloc v = S.Uloc v) ∧ (∀ (x : C'.lev.U) (x' : S.U) (x'' : topU S.U t Θ d), x.1 = x'.1 → x.1 = x''.1 → C'.lev.chi x = S.chi x' * ψ x'') ∧ (∀ c, (C'.y c).1 = y c) ∧ ∀ c s, (C'.stabI c s).1 = ufGL E n (gm c s) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | exact GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | (intros; apply GlobalTheory.Mem.Col2.TopCh.exists_clsG_top <;> assumption)
end

