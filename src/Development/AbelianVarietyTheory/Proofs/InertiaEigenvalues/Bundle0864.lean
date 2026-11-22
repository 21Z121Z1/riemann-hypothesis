import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0122
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0863
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefMapNormEquivariantBasisOfPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0861
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

variable {D : D7} {ρ : Setup D.ntw}

theorem de_mem_eO (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem e_mem_eO (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : ρ.e i b a ^ n = 1) : ρ.e i b a ∈ (ρ.eO i b).range := by
  have h1 : a ^ n = 1 := (ρ.e i b).injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral (D.ntw.O i) a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨y, rfl⟩

theorem typeCharacterExtension_value_mem_coefficientRing {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) (g : G0 (ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (ρ.B i j b).G.P.H (⇑(ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  unfold ext1
  split_ifs with h
  · obtain ⟨g', rfl⟩ := (ρ.eG i j b).surjective g
    have e1 := T.psiU_eq ⟨g', (T.U_eq g').1 h⟩ h
    have hfin : ((ρ.B i j b).G.P.chi ⟨ρ.eG i j b g', h⟩) ^ Nat.card (ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [e1]
    refine e_mem_eO ρ i b (n := Nat.card (ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    rw [← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one]
  · exact one_mem _

theorem card_residueField_of_type {k : Fin 2} {PP : Pl D.host.E} (h : PP ∈ placesOver D.host.E (D.host.g k)) :
    Nat.card (kP PP) = D.host.g k :=
  GlobalTheory.SplitResidueCard.card_quotient_of_ncard (F := D.host.E) (D.host.g_prime k) (D.nd.g_split k) PP h

theorem muC_mem_eO (hρ : ρ.Good)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E} (hPP : PP ∈ (ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨k, hk⟩ := hρ.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hr k _ hz
  have h2 := (D.host.g_prime k).two_le
  have e : ρ.e i b (sideEmb D.ntw i b x) = (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) := (hρ.e_LL0 i b x).trans hx
  rw [← e] at hz ⊢
  exact e_mem_eO ρ i b (Nat.mul_ne_zero (by omega) (by omega)) hz

theorem locC_mem {t : Twist D Circle} (ht : t.Good) {O : Subring ℂ} (h : ∀ x, ((t.chi x : Circle) : ℂ) ∈ O)
    (PP : Pl D.host.E) (w : (kP PP)ˣ) : ((t.locC PP w : ℂˣ) : ℂ) ∈ O := by
  unfold Twist.locC
  split_ifs with hq
  · obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (ht.split.isIdemAt hq) w
    show ((t.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (ht.res PP hq)]
    exact h x
  · simp

theorem levLam_mem_eOk {hρ : ρ.Good}
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b} (T : CellTie hρ D.nexp rd) {k Q ψ} (hψ : TwOK i k Q ψ)
    (x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ)) :
    (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range := by
  obtain ⟨hg, -, hv⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ i j b k Q ψ hψ
  have hle := hρ.range_le i b k
  have e : (ρ.B i j b).levLam (ρ.tw i b k Q ψ) x =
      levFn (ρ.B i j b).F.βS ((ρ.B i j b).levS (ρ.tw i b k Q ψ)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hle (typeCharacterExtension_value_mem_coefficientRing T _)) (prod_mem fun PP hPP => prod_mem fun _ _ => hle (muC_mem_eO hρ hr i j b hPP _)))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (hle (locC_mem (hρ.base i j b).de (de_mem_eO hρ i j b) PP _))
    (locC_mem (O := (ρ.eOk i b k).range) hg (fun z => (hv z).elim fun u hu => ⟨u, hu.symm⟩) PP _)

theorem admT4_of_full_compatibility : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
    ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  intro D ρ hρ rd hT hr E i _ j hj b k Q ψ hψ Sg _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have T := hT.tie i j' b
  rw [IntegralHeckeForms.ThPsi, Submodule.span_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨d, -, hx⟩ := hx
  have hg := (T.thPsi_iff k Q ψ hψ d x).1 hx
  obtain ⟨F, hF, e⟩ := GlobalTheory.T.twistedThetaGenerator_eq_classSum_integralForm D ρ hρ i j' b k Q ψ hψ (levLam_mem_eOk hr T hψ) _ _ _ (T.dat d) _ hg
  obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff k Q ψ hψ F).1 hF
  refine ⟨f, hf, T.injective_rdK k ?_⟩
  rw [T.thP_eq k Q ψ hψ f ⟨x, e⟩]
  exact e.symm

example (X : RealSide D) (hX : FieldOk X) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) : IntegralHeckeForms.admT4 D.nexp E :=
  admT4_of_full_compatibility D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hX.roots E

end GlobalTheory.TwInputs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexCoefficientMapCoreFieldProperties
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AdTh.CoefC

open MvPolynomial

section General

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)

def upL : VV K lam →ₛₗ[φ] VV K' lam where
  toFun := CoefExt.up φ lam
  map_add' x y := Subtype.ext (by simp [CoefExt.up, map_add])
  map_smul' a x := Subtype.ext (by simp [CoefExt.up, smul_eq_C_mul, map_mul, map_C])

theorem upL_apply (v : VV K lam) : upL φ lam v = CoefExt.up φ lam v := rfl

theorem up_id (v : VV K lam) : CoefExt.up (RingHom.id K) lam v = v :=
  Subtype.ext (by simp [CoefExt.up, MvPolynomial.map_id])

theorem up_comp {K'' : Type} [Field K''] (ψ : K' →+* K'') (v : VV K lam) :
    CoefExt.up ψ lam (CoefExt.up φ lam v) = CoefExt.up (ψ.comp φ) lam v :=
  Subtype.ext (by simp [CoefExt.up, MvPolynomial.map_map])

theorem up_bVV_linearIndependent : LinearIndependent K' fun j => CoefExt.up φ lam (bVV K lam j) := by
  classical
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · intro v _
    obtain ⟨a, rfl⟩ := CoefExt.exists_coord φ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Module.finrank_eq_card_basis (bVV K' lam)]

theorem up_linearIndependent (ψ : K →+* ℂ) {m : ℕ} (b : Fin m → VV K lam) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun j => CoefExt.up ψ lam (b j) :=
  CoefExt.linearIndependent (φ := RingHom.id K) (c₀ := upL ψ lam) (c' := upL ψ lam)
    (fun v => by rw [upL_apply, up_id]; rfl) (up_bVV_linearIndependent ψ lam) b hb

theorem injective_of_basis {W : Type} [AddCommGroup W] [Module K W] {ι : Type} [Fintype ι] (B : Module.Basis ι K (VV K lam))
    (c : VV K lam →ₗ[K] W) (h : LinearIndependent K fun j => c (B j)) : Function.Injective c := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hs : ∑ j, B.repr x j • c (B j) = 0 := by
    rw [← hx]
    conv_rhs => rw [← B.sum_repr x]
    simp only [map_sum, map_smul]
  have h0 := Fintype.linearIndependent_iff.1 h _ hs
  rw [← B.sum_repr x]
  simp [h0]

end General

end GlobalTheory.AdTh.CoefC

open GlobalTheory.AdTh.CoefC in
set_option maxHeartbeats 800000 in

theorem GlobalTheory.AdTh.CoefC.coefMap_complex_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ (hw : VsV D i T.Q.c.F), hwOK T.Q.c (lamV D i) hw → ‖c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) hw)‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (rhoM T.Q.c (fun τ => embF T.Q.c (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v)) = (R.cV i).ρ γ (c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v))) ∧ Submodule.span ℂ (Set.range fun v => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v)) = ⊤ ∧ (∀ (m : ℕ) (b : Fin m → VsV D i T.Q.c.F), LinearIndependent T.Q.c.F b → LinearIndependent ℂ (fun j => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (b j)))) ∧ Function.Injective c0 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hT i hstd c0 hc hw hwo
  obtain ⟨gramR, c0R, c0L, hT', hC⟩ := hc
  have hE : ∀ v : VsV D i D.what₂.LL, c0 (CoefExt.up D.what₂.embLL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw', h⟩ := hC v
    rw [show CoefExt.up D.what₂.embLL (lamV D i) v = w from Subtype.ext hw'.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT'.mapL i

  have hli : ∀ (m : ℕ) (b : Fin m → VsV D i ℂ), LinearIndependent ℂ b → LinearIndependent ℂ fun j => c0 (b j) :=
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) (c' := c0) hE h2 b hb
  have hinj : Function.Injective c0 := by
    classical
    let B := (bVV ℂ (lamV D i)).reindex (Fintype.equivFin _)
    refine injective_of_basis (lamV D i) B c0 ?_
    exact hli _ _ B.linearIndependent
  refine ⟨?_, ?_, ?_, fun m b hb => hli m _ (up_linearIndependent _ _ b hb), hinj⟩
  ·
    have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hstd
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hstd.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up (inC T.Q.c) (lamV D i) hw = CoefExt.up D.what₂.embLL (lamV D i) v := by
      apply Subtype.ext
      show MvPolynomial.map (inC T.Q.c) (hw : Pol T.Q.c.F D.what₂.Tau (Vc D i).rank) =
        MvPolynomial.map D.what₂.embLL (Formalism.L2.DIV.ten _)
      have hw' := hwo
      unfold hwOK at hw'
      rw [hw', GlobalTheory.Proof.TensorMapDescent.map_ten, GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      rw [Formalism.L2.DIV.map_extremal, Formalism.L2.DIV.map_extremal]
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT'.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  ·
    intro γ γE hγ v
    let alg := algebraMap T.Q.c.F D.what₂.LL
    have hres : D.what₂.embLL.comp alg = inC T.Q.c := res_embLL T hT.alg hT.laws.pins.2.2.1
    have hup : ∀ w : VsV D i T.Q.c.F, c0 (CoefExt.up (inC T.Q.c) (lamV D i) w) = c0L i (CoefExt.up alg (lamV D i) w) := by
      intro w
      rw [← hE, up_comp, hres]
    have hlab : (fun τ => alg.comp (embF T.Q.c (tauE D τ))) = labLL D := by
      funext τ
      apply RingHom.ext
      intro x
      apply D.what₂.embLL.injective
      have e1 := RingHom.congr_fun (embV_spec (σ' := RingHom.id ℂ) D.what₂.embLL (by rfl) τ) x
      have e2 := RingHom.congr_fun hres (embF T.Q.c (tauE D τ) x)
      exact e2.trans e1.symm
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    rw [hup, hup, rhoM, dif_pos hu, hγE, CoefExt.up_rhoVr, hlab]
    exact h1 γ γE hγ _
  ·
    have hs := CoefExt.span_top (W := (R.cV i).W) (c' := c0) hE h3
    refine top_le_iff.1 (hs ▸ Submodule.span_le.2 ?_)
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := CoefExt.exists_coord (inC T.Q.c) (lamV D i) w
    rw [map_sum]
    exact Submodule.sum_mem _ fun j _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntUnitRoot
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntegralHilbertNinety

theorem conj_sig (D : D7) : Formalism.L2.DIV.IsConjOf D.sp.cm.sig := by
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => ?_⟩
  · have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun e => (D.sp.cm.fixed e).1 (AlgHom.congr_fun h0 e)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩)).symm.trans (Module.finrank_self _)
    have := D.sp.cm.deg2
    omega
  · exact (D.sp.cm.fixed e).1 he

theorem swap_sig (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.IndefR.Lev.swapAE D (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig _ (Formalism.IndefR.Lev.swapAE D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

abbrev swapEquiv (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem swapEquiv_apply (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    swapEquiv D w = Formalism.IndefR.Lev.swapAE D w := rfl

set_option maxHeartbeats 2000000 in

theorem exists_int_unit_root : ∀ (D : D7) (z : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ),
    (z : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D →
    (∃ y₀ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
      z * sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E)) →
    ∃ y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  intro D z hz ⟨y₀, hy₀⟩
  have hss : ∀ w, sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig w) = w := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show a ⊗ₜ[D.host.F] (D.sp.cm.sig (D.sp.cm.sig x)) = a ⊗ₜ[D.host.F] x
      rw [(conj_sig D).2.1 x]
    | add a b ha hb => rw [map_add, map_add, ha, hb]

  have hzs : (z : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig z = 1 := by
    have h1 : sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
        sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      conv_lhs => rw [hy₀]
      rw [map_mul, hss]
    have h2 : (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      rw [mul_assoc, ← h1]; exact hy₀
    have h3 := congrArg (· * ((y₀⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E)) h2
    simp only [Units.mul_inv, mul_assoc, mul_one] at h3
    exact h3.symm
  have hzinv : ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig z := Units.inv_eq_of_mul_eq_one_right hzs

  obtain ⟨z', hz'⟩ : ∃ z' : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) = Formalism.IndefR.Lev.swapAE D z :=
    ⟨Units.map (Formalism.IndefR.Lev.swapAE D).toMonoidHom z, Units.coe_map _ _⟩
  have hconj : ∀ u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      ((Formalism.L2.DIV.conjId D.sp.cm.sig u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (u : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    intro u
    rw [Formalism.L2.DIV.conjId, Units.coe_map]
    rfl
  have hU1 : z' ∈ Formalism.L2.DIV.U1 D.sp.cm.sig := by
    rw [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply]
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hconj, hz', ← swap_sig, ← map_mul, hzs, map_one]
  have hz'inv : ((z'⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      Formalism.IndefR.Lev.swapAE D ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hz', ← map_mul, Units.mul_inv, map_one])
  have hint : z' ∈ Formalism.L2.DIV.intU D.host.F D.host.E := by
    rw [Formalism.L2.DIV.intU, Submonoid.mem_units_iff]
    refine ⟨?_, ?_⟩
    · rw [hz']
      exact (GlobalTheory.IdemSupport.mem_intAE_iff _).1 hz
    · rw [hz'inv]
      refine (GlobalTheory.IdemSupport.mem_intAE_iff _).1 ?_
      rw [hzinv]
      exact GlobalTheory.DetOnto.sigR_mem_intAE D hz
  obtain ⟨x, hx, hxz, -⟩ := GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial D.host.F D.host.E D.sp.cm.sig (conj_sig D)
    (GlobalTheory.HeckeAdjoint.unramified_host D) z' hU1 hint
  have hx' := (Submonoid.mem_units_iff _ _).1 hx
  have hxe : (x : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) * Formalism.UG.sigR D.sp.cm.sig _ (x : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    have h := congrArg (fun u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ =>
      ((u * Formalism.L2.DIV.conjId D.sp.cm.sig x : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) hxz
    simp only [Formalism.L2.DIV.h90, MonoidHom.div_apply, MonoidHom.id_apply, div_mul_cancel] at h
    rw [Units.val_mul, hconj] at h
    exact h
  refine ⟨Units.map (swapEquiv D).symm.toRingHom.toMonoidHom x, ?_, ?_, ?_⟩
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply]
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.1
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply, ← map_inv]
    change swapEquiv D ((swapEquiv D).symm ((x⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.2
  · apply (swapEquiv D).injective
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) =
      swapEquiv D ((z : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)))
    rw [RingEquiv.apply_symm_apply, map_mul, swapEquiv_apply, swapEquiv_apply, swap_sig, ← swapEquiv_apply D
      ((swapEquiv D).symm _), RingEquiv.apply_symm_apply, ← hz']
    exact hxe

end GlobalTheory.IntegralHilbertNinety
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_preimage_of_supportedAtPlace : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ k : GA D V, SuppF V f k → ∃ a : GlobalTheory.FinZeta.Gv V v, GlobalTheory.FinZeta.embV V v a = k := by
  first | exact @GlobalTheory.RawLift.suppF_finIdem_mem_range | exact GlobalTheory.RawLift.suppF_finIdem_mem_range | (intros; apply GlobalTheory.RawLift.suppF_finIdem_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevelStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipScalar_mem_coefficientRing_auxiliaryLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l pd : ℕ), ChiData χW χ M₀ → l.Prime → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime pd (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT pd x → flipScal χW V W T pd x ∈ O := by
  first | exact @GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit | exact GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit | (intros; apply GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficient_extremal_eq_discreteSeries : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), Formalism.IndefR.FWT.IsExtVec (R.MW i (sg0 D A)) (fun ρ => ((v ρ : (R.MW i (sg0 D A)).sm ρ))) → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.FockCoef.coef_extremal | exact GlobalTheory.RawLift.FockCoef.coef_extremal | (intros; apply GlobalTheory.RawLift.FockCoef.coef_extremal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSumsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_spanned_by_thetaSeries_of_classSums : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  first | exact @GlobalTheory.TwInputs.spanGood_of_sumOnto | exact GlobalTheory.TwInputs.spanGood_of_sumOnto | (intros; apply GlobalTheory.TwInputs.spanGood_of_sumOnto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HalfTranslatesLeLevelHalfTranslatesOfDvdStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfTranslates_le_levelHalfTranslates_of_dvd : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e₂ e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsHalfIdem l₂ e₂ → IsIdemSum e' P' → (∀ PP ∈ P', l₂.Mb ≤ PP.asIdeal) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (M : ℕ) (O : Subring ℂ), trSp ψ V W ΛV ΛW f₀ e' M O ≤ trSp ψ V W ΛV ΛW f₀ e₂ M O := by
  first | exact @GlobalTheory.LevelSeries.trSp_le_of_subhalf | exact GlobalTheory.LevelSeries.trSp_le_of_subhalf | (intros; apply GlobalTheory.LevelSeries.trSp_le_of_subhalf <;> assumption)
end

