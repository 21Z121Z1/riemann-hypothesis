import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedThKerEntC
section
noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_hecke {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n) (hord : ξ.OrderDvd n)
    (mt : ℕ → D.Dt →* ℂˣ) (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.KerJ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.KerEntTrue

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem powRatAll_true (l : I.Laws) (Z : TC.Later B (I.cols l)) : GL3Theta.PowRatAll (I.rec7 l Z) := by
  obtain ⟨idl, h⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  exact GL3Theta.powRatAll_of _ idl h (GlobalTheory.KernelScalarUnit.normOne_pow _)

theorem mtType_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) :
    MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_hecke T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

theorem rhoAlg_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) :
    GL3Columns.RhoAlg (O u a) := by
  have h3 := GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType _ u ((I.rec7 l Z).chTw u a) (O u a).mt (mtType_std I hok hp l Z hO u a)
  have hq := powRatAll_true I l Z
  intro i hi
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt i c)
    exact ((h3 i hi).1 _ h z hz).1.1
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt (i + 1) c')
    exact ((h3 i hi).1 _ h z hz).2.1

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G in

theorem adaptedTh_kerEntC {D : D7} {P : Examples₂.EntPl D} {O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)} {Bs : PlaceMatrixFamily D} {Dx : DivX D} {Tw : TwForms D}
    (hB : BasOk P O Bs) (hA : AdaptedEnt P O Bs Dx) (h : KerEntHyp P O Bs Dx Tw) : AdaptedTh (kerEntC P O Bs h) O := by
  intro w hw u μ hl
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hA w hw u μ hl
  refine ⟨Pm, h1, h2, h3, fun i hi c c' => ?_⟩
  show thAtW P O Bs u μ w i c c' = _
  unfold thAtW
  congr 1
  funext k j
  unfold adCoef
  split_ifs with hk
  · set s := Formalism.MainNotions.TaylorLogMetric.lamC (P.lam w) ((O u μ).dgen k.1) with hs
    have hs0 : s ≠ 0 := by
      intro h0
      have hd := (hB u μ w (i + 1) hi c' k.1).1
      haveI hne : Nonempty (Fin (D.R.N (i + 1))) := ⟨j.2.2⟩
      rw [h4 (i + 1) hi c' k.1, ← hs, h0, _root_.inv_zero, zero_pow (by omega), zero_smul] at hd
      exact hd Matrix.det_zero
    have hdet : ((Pm i c k.1).map (tauEmb D (P.lam w) k.1)).det ≠ 0 := (h1 i hi.le c k.1).1
    have ht : s⁻¹ ^ i ≠ 0 := pow_ne_zero _ (inv_ne_zero hs0)
    have hinv : (s⁻¹ ^ i • (Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ =
        (s⁻¹ ^ i)⁻¹ • ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    rw [h4 (i + 1) hi c' k.1, h4 i hi.le c k.1, ← hs, hinv]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e : (1 : ℂ_[D.what₂.places.resChar w]) * s * s⁻¹ ^ (i + 1) * (s⁻¹ ^ i)⁻¹ = 1 := by
      rw [inv_pow, inv_pow, inv_inv, pow_succ]
      field_simp
    simp only [show (kerEntC P O Bs h).lam w = P.lam w from rfl]
    generalize ((Pm (i + 1) c' k.1).map (tauEmb D (P.lam w) k.1)) k.2.1 j.2.2 = x
    generalize ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ j.2.1 k.2.2 = y
    linear_combination (x * y) * e
  · rfl

end GlobalTheory.Mem.Col2.KerEntTrue

theorem GlobalTheory.Mem.Col2.TC.kerEnt_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∃ E : KerEnt (I.rec7 l Z) Y (I.tw l l0 Z), E.lam = Pl.lam ∧ EntOk E O := by
  intro B X I hok hp l Z l0 Y O Pl hq hs hu hj
  choose Pm h1 h2 h3 using AdaptedBases.exists_sys Pl O
  have hU := AdaptedBases.dgenUnitAd Pl O
  have hB : BasOk Pl O (fun u μ w i c τ => (Pm w u μ i c τ).map (Formalism.MainNotions.TaylorLogMetric.tauEmb _ (Pl.lam w) τ)) :=
    fun u μ w i hi c τ => h1 w u μ i hi c τ
  have hC := GlobalTheory.T.toy_entPl_canOnto _ Pl
  have h := GlobalTheory.T.kernelEntryHyp_of_trueColumnChoices I hok hp l Z l0 Y O Pl _ hq hs hB
    (fun u a w _ i _ c τ j k => GlobalTheory.KerRescale.tauEmb_mem Pl w τ (Pm w u a i c τ j k)) hu hj
  exact ⟨GlobalTheory.KerRescale.kerEntR Pl O _ (GlobalTheory.KerRescale.adUnit Pl O) (GlobalTheory.KerRescale.norm_adUnit Pl O hU) h, rfl,
    ⟨fun u μ w _ => GlobalTheory.KerRescale.tieR Pl O _ _ _ hB hC h u μ w,
      fun u μ w _ => GlobalTheory.KerRescale.tieR_un Pl O _ _ _ hB hC h u μ (KerEntTrue.rhoAlg_std I hok hp l Z hs u μ) w⟩,
    GlobalTheory.KerRescale.adaptedTh_kerEntR Pl O hU Pm h1 h2 h3 h⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFamilyCoefficientMapsMulRootOfUnity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

open Formalism.DivisionValues

variable {D : D7}

theorem exists_unit_of_pow (a : D.what₂.LL) (n : ℕ) (hn : n ≠ 0) (ha : a ^ n = 1) :
    ∃ u : (𝓞 D.what₂.LL)ˣ, ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = a ∧ a ∈ Formalism.DivisionValues.cmMax D.what₂.LL ∧ star a * a = 1 := by
  have hσ : ∀ σ : D.what₂.LL →+* ℂ, ‖σ a‖ = 1 := fun σ => by
    have h : (σ a) ^ n = 1 := by rw [← map_pow, ha, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one h hn
  have hconj : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun z hz => by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  have a0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at ha
    exact zero_ne_one ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 a0
  have h2 : star a * a = 1 := D.what₂.embLL.injective (by
    rw [map_mul, D.starLL_cx, hconj _ (hσ _), inv_mul_cancel₀ m0, map_one])
  have hs : star a = a⁻¹ := eq_inv_of_mul_eq_one_left h2
  have h1 : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
    change ∀ σ : D.what₂.LL →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
    intro σ
    rw [hs, map_inv₀, hconj _ (hσ σ)]
  have hi : IsIntegral (𝓞 D.what₂.LL) a := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [ha]
    exact isIntegral_one
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hx1 : x ^ n = 1 := IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [map_pow, hx, ha, map_one])
  refine ⟨(IsUnit.of_pow_eq_one hx1 hn).unit, ?_, h1, h2⟩
  rw [IsUnit.unit_spec]
  exact hx

theorem coefMapTie_smul {V C lam c0 rho} (h : Formalism.IndefR.Bridge.CoefMapTie (D := D) V C (lam := lam) c0 rho) {μ : ℂ} (hμ : μ ≠ 0) :
    Formalism.IndefR.Bridge.CoefMapTie V C (μ • c0) rho := by
  obtain ⟨a1, a2, a3⟩ := h
  refine ⟨fun γ γE hγ v => by simp [a1 γ γE hγ v], a2.units_smul fun _ => Units.mk0 _ hμ, ?_⟩
  rw [eq_top_iff, ← a3, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have := Submodule.smul_mem _ μ⁻¹ (Submodule.subset_span (R := ℂ)
    (s := Set.range fun i => (μ • c0) (bVV D.what₂.LL lam i)) ⟨i, rfl⟩)
  exact Set.mem_of_eq_of_mem (inv_smul_smul₀ hμ (c0 _)).symm this

theorem coefTie_smul {V C S J χ P lam c0 pair nab del}
    (h : Formalism.IndefR.Bridge.CoefTie (D := D) V C (S := S) (J := J) (χ := χ) P lam c0 pair nab del)
    (l : D.what₂.LL) (u : (𝓞 D.what₂.LL)ˣ) (hu : ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = l) (h1 : l ∈ Formalism.DivisionValues.cmMax D.what₂.LL)
    (h2 : star l * l = 1) :
    Formalism.IndefR.Bridge.CoefTie V C P lam (D.what₂.embLL l • c0) pair nab del := by
  have l0 : l ≠ 0 := right_ne_zero_of_mul_eq_one h2
  have m0 : D.what₂.embLL l ≠ 0 := (map_ne_zero _).2 l0
  have li : (((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) : D.what₂.LL) = l⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← hu, ← map_mul (algebraMap (𝓞 D.what₂.LL) D.what₂.LL), Units.inv_mul, map_one])
  obtain ⟨e, a1, a2, a3, a4, a5⟩ := h
  let s := LinearEquiv.smulOfNeZero D.what₂.LL (VV D.what₂.LL lam) l⁻¹ (inv_ne_zero l0)
  have hs : ∀ x, (e.trans s) x = l⁻¹ • e x := fun _ => rfl
  have hm : ∀ N : Submodule (𝓞 D.what₂.LL) S.V,
      N.map ((e.trans s).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) =
        N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := fun N => by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      exact (map_smul e _ _).trans (congrArg (· • e v) li)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(u : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      show (e.trans s) ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL)) • v) = e v
      rw [show algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL) = l from hu]
      exact (hs _).trans ((congrArg (l⁻¹ • ·) (map_smul e l v)).trans (inv_smul_smul₀ l0 _))
  refine ⟨e.trans s, fun i j => ?_, fun x => ?_, fun x x' => ?_, fun c => (hm _).trans (a4 c), fun c => (hm _).trans (a5 c)⟩
  · rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem (inv_mem h1) (a1 i j)
  · rw [hs, LinearMap.smul_apply, map_smulₛₗ, map_inv₀, smul_inv_smul₀ m0, a2]
  · rw [hs, hs, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, a3, smul_smul, starRingEnd_apply, star_inv₀,
      ← mul_inv, mul_comm, h2, inv_one, one_smul]

end GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

namespace GlobalTheory.Mem.R3.Rw.OmExt

set_option maxHeartbeats 1000000 in

theorem coefFam_update_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W),
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R c0L → ∀ (i : Fin D.R.m) (a : D.what₂.LL) (n : ℕ), n ≠ 0 → a ^ n = 1 →
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R (Function.update c0L i (D.what₂.embLL a • c0L i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R c0L hc i a n hn ha
  obtain ⟨u, hu, h1, h2⟩ := RootUpd.exists_unit_of_pow a n hn ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 (right_ne_zero_of_mul_eq_one h2)
  obtain ⟨gramR, c0R, ht⟩ := hc
  refine ⟨gramR, c0R, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ht.ok, ht.gramR_eq, ht.mapR, fun j => ?_,
    ht.coefR, fun j t => ?_⟩⟩
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefMapTie_smul (ht.mapL j) m0
    · rw [Function.update_of_ne hj]
      exact ht.mapL j
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefTie_smul (ht.coefL j t) a u hu h1 h2
    · rw [Function.update_of_ne hj]
      exact ht.coefL j t

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLatBC

set_option maxHeartbeats 4000000 in

theorem lift_lattice_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ N : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective N.mulVec ∧
          (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec N fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).tC z'.F.cr false j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec N fun k => φ (x k)))) ((z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (GlobalTheory.T.extendedData_lift_blockDatum_baseChange_one_matrix h1 h2 h3 h4 h5 h6 h7) (StepW.of_all fun K B' f' T' w' _ _ hQ => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  obtain ⟨e, C, hC, hθ⟩ := hQ B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  have hstar : ∀ x, φ (star x) = star (φ x) := fun x => (w'.st Z').toD7.what₂.embLL.injective (by
    rw [hφ, (w.st Z).toD7.starLL_cx, (w'.st Z').toD7.starLL_cx, hφ])
  obtain ⟨N, hN, hTl, hF⟩ := GlobalTheory.T.blockDatum_baseChange_definiteLattice_compatible φ hstar e _ _ _ _ _ _ 1 C (hL.ok.ok2.lifts j _) hC
  refine ⟨N, hN, hTl, fun x => ?_⟩
  refine HEq.trans (heq_of_eq (tC_cpt (z'.R.toCx3 z'.F) z'.F.cr false j' _ _)) (HEq.trans ?_ (heq_of_eq (tC_cpt (z.R.toCx3 z.F) z.F.cr false j _ x)).symm)
  have e1 : z'.F.cr.toL (z'.R.toCx3 z'.F).zs false j' _ (Matrix.mulVec N fun k => φ (x k)) =
      GlobalTheory.Mem.R3.LiftLatBC.bcF φ _ _ C (z.F.cr.toL (z.R.toCx3 z.F).zs false j _ x) := hF x
  exact HEq.trans (heq_of_eq (congrArg (fun y => (z'.R.toCx3 z'.F).θ' j' _ ((z'.R.toCx3 z'.F).jL j' _ y)) e1)) (hθ _)

end GlobalTheory.Mem.R3.LiftLatBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBaseLatticeEqSpanImagesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_lift_baseLattice_eq_span_images : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        (z'.R.FW j').Mj (z'.F.lv2.lvl false).P (z'.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.X).coeff g) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) {x' | ∃ x ∈ (z.R.FW j).Mj (z.F.lv2.lvl false).P (z.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.X).coeff g), ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  first | exact @GlobalTheory.Mem.R3.LiftForms.lift_Mj_base | exact GlobalTheory.Mem.R3.LiftForms.lift_Mj_base | (intros; apply GlobalTheory.Mem.R3.LiftForms.lift_Mj_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBlockDatumEqBaseChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_lift_blockDatum_eq_baseChange : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ e, GlobalTheory.Mem.R3.DefLatBC.BlockBaseChange φ e ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)
          ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0) ((zsOf z.R z.F).Zl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((zsOf z'.R z'.F).Zl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) := by
  first | exact @GlobalTheory.Mem.R3.TwistedPlaceExtensions.blockBC_lift | exact GlobalTheory.Mem.R3.TwistedPlaceExtensions.blockBC_lift | (intros; apply GlobalTheory.Mem.R3.TwistedPlaceExtensions.blockBC_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric

theorem inner_theta_eq_lam : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t p _ x hx hW x'
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  have hK := GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  set K := (LinearMap.ker θ)ᗮ with hKdef
  have hS := GlobalTheory.T.liftThetaMap_labelPartPreimage_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p x (hK ▸ hx) hW

  have hkerK : ∀ z, z - K.starProjection z ∈ LinearMap.ker θ := by
    intro z
    have := K.sub_starProjection_mem_orthogonal z
    rwa [Submodule.orthogonal_orthogonal] at this
  have hKperp : ∀ z, z - K.starProjection z ∈ Kᗮ := fun z => K.sub_starProjection_mem_orthogonal z

  have hgoodK : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ q ∈ K,
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ q⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), q⟫_ℂ := by
    intro a ha q hq
    rw [hK] at hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact GlobalTheory.T.liftThetaMap_inner_eq_lambda_mul_rationalVectors D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p a b ha
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add, inner_add_right, inner_add_right, h1, h2, mul_add]
    | smul c y _ h => rw [map_smul, inner_smul_right, inner_smul_right, h]; ring
  have hgood : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ x',
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ := by
    intro a ha x'
    have huK : D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) ∈ K := by rw [hK]; exact Submodule.subset_span ⟨a, rfl⟩
    have e1 : θ x' = θ (K.starProjection x') := by
      have := hkerK x'
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e2 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ = ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), K.starProjection x'⟫_ℂ := by
      have h0 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x' - K.starProjection x'⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal huK (hKperp x')
      rw [inner_sub_right, sub_eq_zero] at h0; exact h0
    rw [e1, e2]
    exact hgoodK a ha _ (K.starProjection_apply_mem x')
  clear hx hW
  induction hS using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact hgood a ha x'
  | zero => simp
  | add y z _ _ h1 h2 => rw [map_add, inner_add_left, inner_add_left, h1, h2, mul_add]
  | smul c y _ h => rw [map_smul, inner_smul_left, inner_smul_left, h]; ring

end GlobalTheory.Mem.R3.LamMetric
end

