import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0455
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0329
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumPairUniformLevelBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D}

def divPts (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) : AddSubgroup (WO S T) where
  carrier := {y | c • y = y ∧ N • y ∈ Λ}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], by rw [nsmul_add]; exact Λ.add_mem hx2 hy2⟩
  zero_mem' := ⟨smul_zero _, by rw [nsmul_zero]; exact Λ.zero_mem⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], by rw [smul_neg]; exact Λ.neg_mem hx2⟩

theorem mem_divPts {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} {y : WO S T} :
    y ∈ divPts Λ c N ↔ c • y = y ∧ N • y ∈ Λ := Iff.rfl

abbrev DQ (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) :=
  ↥(divPts Λ c N) ⧸ (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N)

noncomputable def rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) : ↥(divPts Λ c N) :=
  (QuotientAddGroup.mk_surjective q).choose

theorem mk_rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) :
    (QuotientAddGroup.mk (rep q) : DQ Λ c N) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

theorem rep_injective {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} :
    Function.Injective fun q : DQ Λ c N => ((rep q : ↥(divPts Λ c N)) : WO S T) := by
  intro q₁ q₂ h
  rw [← mk_rep q₁, ← mk_rep q₂, Subtype.ext h]

variable (ψ : AddChar (AF D.host.F) ℂ)

noncomputable def qChar (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) (t : WO S T)
    (ht : ∀ g ∈ Λ, ψ (symplO S T t g) = 1) : AddChar (DQ Λ c N) ℂ where
  toFun q := Quotient.liftOn' q (fun y => ψ (symplO S T t y)) (fun y₁ y₂ h => by
    have h' := QuotientAddGroup.leftRel_apply.mp h
    rw [AddSubgroup.mem_addSubgroupOf] at h'
    have : ((y₂ : ↥(divPts Λ c N)) : WO S T) = y₁ + ((-y₁ + y₂ : ↥(divPts Λ c N)) : WO S T) := by
      push_cast; abel
    rw [this, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul, ht _ h'.1, mul_one])
  map_zero_eq_one' := by
    change ψ (symplO S T t 0) = 1
    rw [GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one]
  map_add_eq_mul' q₁ q₂ := by
    induction q₁ using QuotientAddGroup.induction_on with
    | H y₁ =>
    induction q₂ using QuotientAddGroup.induction_on with
    | H y₂ =>
    change ψ (symplO S T t ((y₁ + y₂ : ↥(divPts Λ c N)) : WO S T)) = ψ (symplO S T t y₁) * ψ (symplO S T t y₂)
    rw [AddSubgroup.coe_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul]

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

end GlobalTheory.DivPtFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def CopyTw.cm (h : CopyTw D D' ι e) (j : Fin D.R.m) : Fin D'.R.m :=
  Fin.cast (congrArg Ranks.m h.gal.R) j

theorem CopyTw.cm_val (h : CopyTw D D' ι e) (j : Fin D.R.m) : ((h.cm j : Fin D'.R.m) : ℕ) = j := rfl

abbrev SameSetup (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) : Prop := SameData ρ ρ'

theorem SameSetup.refl (ρ : Setup D.ntw) : SameSetup ρ ρ := SameData.refl ρ

def RdRel (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (f : D.nexp.Fm i ((j : ℕ) + 1) b),
    HEq (rd' i' (h.cm j) b (h.fmCast hi ((j : ℕ) + 1) b f)) (rd i j b f)

theorem RdRel.refl (D : D7) {ρ : Setup D.ntw} (rd : Rds D.nexp ρ) : RdRel (CopyTw.refl D) rd rd := fun i i' hi j b f => by
  cases hi; exact HEq.rfl

end GlobalTheory.TwInputs.Move

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanConjUnitaryLieAlgebraRealPlaceEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LieSpanConj

theorem exists_decomp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 ∧ Yᴴ * H + H * Y = 0 ∧
      Z = X + Complex.I • Y := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  set Zb : Matrix (Fin n) (Fin n) ℂ := -(H⁻¹ * Zᴴ * H) with hZb
  have hA : Zbᴴ * H = -(H * Z) := by
    rw [hZb, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, hH, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  have hB : H * Zb = -(Zᴴ * H) := by
    rw [hZb, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z + Zb), (-(Complex.I / 2)) • (Z - Zb), ?_, ?_, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      hA, hB]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    rw [show Zᴴ * H + -(H * Z) + (H * Z + -(Zᴴ * H)) = 0 by abel, smul_zero]
  · rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      hA, hB]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.conj_I]
      ring
    rw [this]
    rw [show Zᴴ * H - -(H * Z) = H * Z + Zᴴ * H by abel, show H * Z - -(Zᴴ * H) = H * Z + Zᴴ * H by abel]
    rw [← add_smul]
    simp
  · rw [smul_smul, smul_add, smul_sub]
    have h1 : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      have := Complex.I_sq
      linear_combination (-(1 / 2 : ℂ)) * this
    rw [h1]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem span_conj_lieAt_eq_top : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (Fm : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit Fm → Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} = ⊤ := by
  intro D V τ Fm hF
  have hFd : IsUnit Fm.det := (Matrix.isUnit_iff_isUnit_det Fm).1 hF
  have hd : (gramAt D V τ).det ≠ 0 := by
    rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)
  rw [eq_top_iff]
  intro Z' _
  obtain ⟨X, Y, hX, hY, hZ⟩ :=
    GlobalTheory.LieSpanConj.exists_decomp (gramAt D V τ) (SmoothForms.RealPts.gramAt_herm V τ) hd (Fm⁻¹ * Z' * Fm)
  have hmX : Fm * X * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨X, hX, rfl⟩
  have hmY : Fm * Y * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨Y, hY, rfl⟩
  have hZ' : Z' = Fm * X * Fm⁻¹ + Complex.I • (Fm * Y * Fm⁻¹) := by
    have : Z' = Fm * (Fm⁻¹ * Z' * Fm) * Fm⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hFd, Matrix.mul_one]
    rw [this, hZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hZ']
  exact Submodule.add_mem _ hmX (Submodule.smul_mem _ _ hmY)

end GlobalTheory.LieSpanConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericType
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)]
    (U : Subgroup (G0g D.nd)) [Fintype U],
    U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r →
    ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ →
    2 ≤ D.R.r → ∃ v : MonoidAlgebra ℂ (G0g D.nd),
      GlobalTheory.MeetsGen.uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 * v = 1 := by
  intro D S _ U _ hU ψ hψ hr
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  exact GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement U ψ D.ntypes.e0 hi (fun a => ((Subalgebra.mem_center_iff.mp hc) a).symm)
    (GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero D S U hU ψ hψ hr)

open GlobalTheory.MeetsGen in

theorem GlobalTheory.TwInputs.meetsAll_of_ties : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7), NExpTied D → GrpSide D → MeetsAll D := by
  intro hG D T S i j b W hW hst hfix
  classical
  by_cases hr : D.R.r ≤ 1
  · have hFm0 : Fm0 D.nexp i j b = ⊤ := by
      rw [eq_top_iff]
      intro x _
      simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
      intro u
      have hu1 : u = 1 := Subtype.ext (GlobalTheory.MeetsGen.uup_eq_one_of_le_one _ _ hr _ (T.U_eq ▸ u.2))
      subst hu1
      simp
    rw [hFm0, inf_top_eq]
    exact hW
  have hr : 2 ≤ D.R.r := by omega
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  haveI : Fintype D.nexp.U := Fintype.ofFinite _
  obtain ⟨θ, hθ, hψ⟩ := T.psiU_gen i b
  let s : ↥D.LL0 →+* FractionRing (D.ntw.O i) :=
    (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).comp (if b then D.ntw.emb0 i else D.ntw.emb0b i)
  let t : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom
  let Z : Set (FractionRing (D.ntw.O i)) :=
    {z | ∃ (x : Σ k : Fin 2, D.nd.PlG k) (a : Multiplicative (ZMod (D.host.g x.1))), z = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i))}
  have hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
    rintro z ⟨x, a, rfl⟩
    haveI : NeZero (D.host.g x.1) := ⟨(D.host.g_prime x.1).ne_zero⟩
    refine ⟨Fintype.card (Multiplicative (ZMod (D.host.g x.1))), Fintype.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨E, jE, hsE, hZE, hj⟩ := GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex s t Z hZ

  let θE : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* Eˣ := fun x =>
    { toFun := fun a => ⟨⟨((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a, rfl⟩⟩,
        ⟨(((θ x a)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a⁻¹, by simp⟩⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := by ext; simp
      map_mul' := fun a a' => by ext; simp }
  have hθE : ∀ x a, (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) :=
    fun _ _ => rfl
  let θ' : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ :=
    fun x => (Units.map jE.toMonoidHom).comp (θE x)
  have hθ' : 2 ≤ D.R.r → ∀ x, θ' x ≠ 1 := by
    intro h x h1
    apply hθ h x
    refine MonoidHom.ext fun a => Units.ext ?_
    have h2 := congrArg (fun φ : Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ => ((φ a : ℂˣ) : ℂ)) h1
    simp only [θ', MonoidHom.comp_apply, Units.coe_map, MonoidHom.one_apply, Units.val_one] at h2
    have h3 : ((θE x a : Eˣ) : E) = 1 := jE.injective (by rw [map_one]; exact h2)
    have h4 : (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = 1 := by rw [h3]; rfl
    rw [MonoidHom.one_apply, Units.val_one]
    exact (hθE x a).symm.trans h4
  let ψ' : D.nexp.U →* ℂˣ := (Formalism.L2.NX.psiStd _ _ θ').comp (Subgroup.inclusion T.U_eq.le)
  have hψ' : Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ' :=
    ⟨θ', hθ', fun u => rfl⟩
  obtain ⟨vC, hvC⟩ := GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector D S D.nexp.U T.U_eq ψ' hψ' hr

  have hψE : ∀ u : D.nexp.U, ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) ∈ E := by
    intro u
    rw [hψ u]
    simp only [Formalism.L2.NX.stdVal, Units.coe_prod]
    exact E.prod_mem fun x _ => hZE ⟨x, _, rfl⟩
  let fE : D.nexp.U → E := fun u => ⟨(((D.nexp.psiU i b u)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)),
    by rw [Units.val_inv_eq_inv_val]; exact E.inv_mem (hψE u)⟩
  let eE : MonoidAlgebra E (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => (⟨s (D.nexp.eLL0 g), hsE _⟩ : E))
  have hψval : ∀ u : D.nexp.U, jE ⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ =
      ((ψ' u : ℂˣ) : ℂ) := by
    intro u
    have e1 : (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E) =
        ∏ x, ((θE x (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
          (((u : G0g D.nd) x : GL (Fin D.R.r) (ZMod (D.host.g x.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g x.1))))) : Eˣ) : E) := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_finsetProd, hθE]
      rw [hψ u]
      simp [Formalism.L2.NX.stdVal, Units.coe_prod]
    rw [e1, map_prod]
    simp [ψ', Formalism.L2.NX.psiStd, Formalism.L2.NX.stdVal, θ', Units.coe_prod]
  have hC1 : MonoidAlgebra.mapRingHom (G0g D.nd) jE (uElt D.nexp.U fE eE) =
      uElt D.nexp.U (fun u => (((ψ' u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 := by
    rw [GlobalTheory.MeetsGen.map_uElt]
    congr 1
    · funext u
      have e2 : fE u = (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E)⁻¹ :=
        Subtype.ext (by simp [fE])
      rw [e2, map_inv₀, hψval, Units.val_inv_eq_inv_val]
    · refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
      rw [MonoidAlgebra.coeff_mapRingHom]
      simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
      rw [hj, ← D.nStage_trivialCharacter_coeff_eq]
      rfl
  have hK1 : MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype eE = D.nexp.eAlg i b := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.coeff_mapRingHom, D.nexp.eAlg_def]
    simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
    rfl
  obtain ⟨vE, hvE⟩ := GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field jE (uElt D.nexp.U fE eE) ⟨vC, by rw [hC1]; exact hvC⟩
  have hvK := congrArg (MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype) hvE
  rw [map_mul, map_one, GlobalTheory.MeetsGen.map_uElt, hK1] at hvK
  have heq := GlobalTheory.MeetsGen.eq_sum_of_uElt_mul D.nexp.U _ (D.nexp.eAlg i b) _ (D.nexp.eAlg_idem i b) (D.nexp.eAlg_central i b) hvK
  exact GlobalTheory.T.stable_submodule_meets_character_type_vectors (D.nexp.actG i j b) D.nexp.U (D.nexp.psiU i b) (D.nexp.eAlg i b) _ heq W hW
    (fun g x hx => hst g x hx) (fun x hx => hfix x hx)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunIsotropicMeanUnipotentInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

variable {D : D7}

theorem exists_split (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (hI : IsIsoFrame W I) :
    ∃ (W' : HSp D) (ι : W'.V →ₗ[D.host.E] W.V), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I (frameMat W W' ι) := by
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj W I
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp W.frame.equivFun.toLinearMap hI.2.1
  have hiso : ∀ a b, W.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hI.2.2]; rfl
  obtain ⟨W', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral W e he hiso
  refine ⟨W', ι, ⟨hI, ?_, ?_, by omega⟩⟩
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← W.herm.eq, h3]
    simp

theorem decomp {W W' : HSp D} {s k : ℕ} {I : Matrix (Fin W.rank) (Fin s) D.host.E}
    {B : Matrix (Fin W.rank) (Fin W'.rank) D.host.E} (hsp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I B) (x : Mx D W.rank k)
    (hx : rat (Iᴴ * W.gram) ⬝ x = 0) : ∃ (z : Mx D s k) (w : Mx D W'.rank k), x = rat I ⬝ z + rat B ⬝ w := by
  obtain ⟨d, hde, hdi, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W' s I B hsp
  have h := d.sum_eq_one_rat
  simp only [GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, GlobalTheory.MixModel.HypDec.q0, hde, hdi] at h
  have h1 : rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ x = x := by
    rw [GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [← h, GlobalTheory.MixModel.rat_add, GlobalTheory.MixModel.rat_add, Matrix.add_mul, Matrix.add_mul] at h1
  have h2 : rat (d.e' * (Iᴴ * W.gram)) ⬝ x = 0 := by
    rw [GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc, hx, Matrix.mul_zero]
  rw [h2, add_zero] at h1
  rw [GlobalTheory.MixModel.rat_mul I, GlobalTheory.MixModel.rat_mul B, Matrix.mul_assoc (rat I), Matrix.mul_assoc (rat B)] at h1
  exact ⟨_, _, h1.symm⟩

theorem periodic {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g) {s : ℕ}
    (I : Matrix (Fin W.rank) (Fin s) D.host.E) (p : WO V W) (hp : rat (Iᴴ * W.gram) ⬝ p = 0)
    (γ : Matrix (Fin s) (Fin V.rank) D.host.E) : g (rat I ⬝ rat γ + p) = g p := by
  have e1 : rat I ⬝ rat γ = ratW W V (I * γ) := by rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.rat_mul]
  have e2 : GlobalTheory.MixModel.adj p ⬝ rat (W.gram * I) = 0 := by
    have := congrArg GlobalTheory.MixModel.adj hp
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_zero, ← GlobalTheory.MixModel.rat_conjTranspose, conjTranspose_mul,
      GlobalTheory.MixModel.gram_conjTranspose, conjTranspose_conjTranspose] at this
  have e3 : GlobalTheory.MixModel.adj p ⬝ (GlobalTheory.MixModel.gA W ⬝ ratW W V (I * γ)) = 0 := by
    have e2' : GlobalTheory.MixModel.adj p ⬝ (rat W.gram ⬝ rat I) = 0 := by rw [← GlobalTheory.MixModel.rat_mul]; exact e2
    rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat_mul I γ, ← Matrix.mul_assoc (rat W.gram) (rat I) (rat γ),
      ← Matrix.mul_assoc, e2', Matrix.zero_mul]
  rw [e1, hg.quasi, GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, e3, Matrix.mul_zero, Matrix.trace_zero,
    map_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.TargetUnipMean

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

theorem mean_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ n ∈ NI W I, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, om (1, n) f (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f (HMul.hMul (I.map (incA D)) y + x) ∂ν := by
  intro D ψ V W χV χW om hom s I hI ν 𝓨 hν n hn f hf x hx
  obtain ⟨W', ι, hsp⟩ := exists_split W I hI
  obtain ⟨omt, hmt, hsw⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ V W χV χW om hom
  obtain ⟨μ', 𝓖', hμ', he⟩ := (GlobalTheory.T.weilConstantTerm_source_target_conjAdjoint_corr D V W W' s ι I).1 ν 𝓨 hν
  have hlaw := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W'
  have hlawW := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f) = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f := by
    have h1 := GlobalTheory.UnipRes.res_unip D W W' V s I (frameMat W W' ι) hsp ψ χW χV omt hmt μ' 𝓖' hμ' ⟨n, hn⟩
      (GlobalTheory.PairLift.dag V W f) (hlawW.theta f hf)
    have h2 : GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f)) =
        GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f) := by
      rw [← he, ← he, ← hsw]
      exact h1
    funext w
    have h3 := congrFun h2 (GlobalTheory.PairLift.adjO W' V w)
    simp only [GlobalTheory.PairLift.dag, hlaw.invol] at h3
    exact (starRingEnd ℂ).injective h3
  have hII : Iᴴ * W.gram * I = 0 := hI.2.2
  have hIB : Iᴴ * W.gram * frameMat W W' ι = 0 := hsp.orth
  obtain ⟨z, w, hz⟩ := decomp hsp x hx
  have hred : ∀ g, IsThetaFunO ψ V W g → ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + x) ∂ν =
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 g w := by
    intro g hg
    have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D s V.rank, ∀ a : Mx D s V.rank,
        g (rat I ⬝ (γ + a) + rat (frameMat W W' ι) ⬝ w) = g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w) := by
      intro γ hγ a
      obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
      rw [Matrix.mul_add, add_assoc]
      refine periodic hg I _ ?_ γ0
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hII,
        hIB, GlobalTheory.MixModel.rat_zero, GlobalTheory.MixModel.rat_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero]
    have := GlobalTheory.MixModel.covolOne_integral_add hν (fun a => g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w)) hper z
    rw [hz]
    calc ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + (rat I ⬝ z + rat (frameMat W W' ι) ⬝ w)) ∂ν
        = ∫ y in 𝓨, g (rat I ⬝ (y + z) + rat (frameMat W W' ι) ⬝ w) ∂ν := by
          congr 1
          funext y
          show g (rat I ⬝ y + _) = _
          rw [Matrix.mul_add, add_assoc]
      _ = _ := this
  rw [hred (om (1, n) f) (hom.om_pres (1, n) f hf), hred f hf, hr]

end GlobalTheory.TargetUnipMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumPairUniformLevelBoundStatement
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
theorem _root_.GlobalTheory.T.vacuum_pair_uniform_level_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∃ K : ℕ, ∀ (M : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ) (Φ φ : WO V W → ℂ), M ≠ 0 → Nat.Coprime M (GlobalTheory.Tow.badN D) → IsIdemSum e P → (∀ PP ∈ P, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → zeta M ∈ O → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) M Φ → (∀ x, Φ x ∈ O) → IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ → ((M : ℂ) ^ K) • φ ∈ trSp ψ V W ΛV ΛW f₀ e M O := by
  first | exact @GlobalTheory.LevelFourier.smul_mem_trSp | exact GlobalTheory.LevelFourier.smul_mem_trSp | (intros; apply GlobalTheory.LevelFourier.smul_mem_trSp <;> assumption)
end

