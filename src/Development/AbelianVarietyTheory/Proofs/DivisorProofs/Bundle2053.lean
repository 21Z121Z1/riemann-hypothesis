import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TruncFix

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idem (T : Finset (Pl F)) : AF F := ∑ v ∈ T, GlobalTheory.LatVac.liftV v 1

theorem evFin_liftV_one (v w : Pl F) : evFin F w (GlobalTheory.LatVac.liftV v 1) = if w = v then 1 else 0 := by
  by_cases h : w = v
  · subst h; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
  · rw [if_neg h]; exact GlobalTheory.ThK.LocalOps.evFin_of_at h (GlobalTheory.LatVac.at_liftV v 1)

theorem evFin_idem (T : Finset (Pl F)) (w : Pl F) : evFin F w (idem T) = if w ∈ T then 1 else 0 := by
  classical
  simp only [idem, map_sum, evFin_liftV_one]
  rw [Finset.sum_ite_eq]

theorem idem_mul_idem (T : Finset (Pl F)) : idem T * idem T = idem T := by
  classical
  conv_lhs => rw [idem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, ← idem, evFin_idem, if_pos hv]

theorem idem_insert {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) :
    idem (insert v T) = GlobalTheory.LatVac.liftV v 1 + idem T := by
  classical
  rw [idem, Finset.sum_insert hv]; rfl

theorem liftV_mul_idem {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) : GlobalTheory.LatVac.liftV v 1 * idem T = 0 := by
  classical
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, evFin_idem, if_neg hv, map_zero]

theorem idem_singleton (v : Pl F) : idem ({v} : Finset (Pl F)) = GlobalTheory.LatVac.liftV v 1 := by
  simp [idem]

def truncMat {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := 1 + e • (A - 1)

theorem truncMat_mul {n : ℕ} {e : AF F} (he : e * e = e) {A B : Matrix (Fin n) (Fin n) (AE F E)} (h : A * B = 1) :
    truncMat e A * truncMat e B = 1 := by
  simp only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, h]
  have he2 : e ^ 2 = e := by rw [sq, he]
  match_scalars <;> ring_nf <;> simp only [he2] <;> ring

theorem truncMat_transpose {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    (truncMat e A)ᵀ = truncMat e Aᵀ := by
  simp [truncMat, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub]

theorem truncMat_map (σ : E →ₐ[F] E) {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    (truncMat e A).map (cA σ) = truncMat e (A.map (cA σ)) := by
  ext i j
  by_cases h : i = j <;> simp [truncMat, Matrix.one_apply, h]

theorem truncMat_unitary {n : ℕ} {e : AF F} (he : e * e = e) {A Ab J : Matrix (Fin n) (Fin n) (AE F E)}
    (h : Aᵀ * J * Ab = J) : (truncMat e A)ᵀ * J * truncMat e Ab = J := by
  have h' : Aᵀ * (J * Ab) = J := by rw [← Matrix.mul_assoc, h]
  rw [truncMat_transpose]
  simp only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h']
  have he2 : e ^ 2 = e := by rw [sq, he]
  match_scalars <;> ring_nf <;> simp only [he2] <;> ring

variable {σ : E →ₐ[F] E}

def truncU (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : UA σ J :=
  ⟨⟨truncMat (idem T) k.1.1, truncMat (idem T) k.1.inv, truncMat_mul (idem_mul_idem T) k.1.val_inv,
    truncMat_mul (idem_mul_idem T) k.1.inv_val⟩, by
    show (truncMat (idem T) k.1.1)ᵀ * incM F J * (truncMat (idem T) k.1.1).map (cA σ) = incM F J
    rw [truncMat_map]
    exact truncMat_unitary (idem_mul_idem T) k.2⟩

theorem mat_truncU (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    mat (truncU T k) = truncMat (idem T) (mat k) := rfl

theorem mat_truncU_inv (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    mat (truncU T k)⁻¹ = truncMat (idem T) (mat k⁻¹) := rfl

theorem truncU_insert {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    truncU (insert v T) k = truncU {v} k * truncU T k := by
  refine Subtype.ext (Units.ext ?_)
  show truncMat (idem (insert v T)) (mat k) = truncMat (idem {v}) (mat k) * truncMat (idem T) (mat k)
  have h0 : GlobalTheory.LatVac.liftV v 1 * idem T = 0 := liftV_mul_idem hv
  rw [idem_insert hv, idem_singleton]
  unfold truncMat
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0,
    zero_smul, add_zero, add_smul]
  abel

theorem truncU_mem_UAt (v : Pl F) {n : ℕ} {X : Spc F E n} (k : UA σ X.J) :
    truncU {v} k ∈ UAt σ X (evFin F v) := by
  intro u hu
  rw [mat_truncU, idem_singleton]
  simp only [truncMat, add_sub_cancel_left, smul_smul]
  rw [mul_comm, GlobalTheory.ThK.LocalOps.liftV_one_mul, hu, map_zero, zero_smul]

end GlobalTheory.TruncFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChain
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnAtPlacesBase

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

theorem on_of_has_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : HasIndexBound O) (hD : LeafData O) (hJ : GlobalTheory.TraceClassRank.RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : HasTwistBound O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hE : HasExpBound N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ∃ err, ONwith S N err := by
  obtain ⟨Th1, a, r1, r2, de2, hT0⟩ := hT0
  obtain ⟨ε, h1⟩ := h1
  obtain ⟨-, Jp, hJS, hJE⟩ := hE
  exact ⟨_, GlobalTheory.TraceClassRank.on_core_atPlaces N
    ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2, ε0 := ε, Jp := Jp } : OnObj S P c) CE hRk
    hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1⟩

end Free

theorem on_base_atPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hO s N C hOk h1 h2 hM hμ hth hU hB hrat hRk hSq hY hSup hSp hS hT0
    hD hJ hI hT2 hT1 hSh hBS hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1
  classical
  obtain ⟨hc, hinj, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  have hN : TieLevelNum O (rankPred D.R) D.R.f := by
    letI := st
    letI := hostAlg D
    refine ⟨hd.f_eq, ?_⟩
    rw [hO.rr_eq, OntoChain.rank_eq]
    push_cast
    rfl
  obtain ⟨w, hw⟩ := GlobalTheory.BigOnBase.exists_tieCoord_base ht (fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩) hOk h1 h2 hM.HV hM.jV hM.HW hμ (phasedLift_one hth) hU hB hrat hI hT2
  obtain ⟨tU, hMk, hP⟩ := level_of_tied ht hOk.irr h1
  exact on_of_has_atPlaces N (withCoord O w) C hRk hMk hSup hP hw hSp hS hT0 hD hJ hI hT2 hT1 hSh
    (leafIndexU_of O D.R.f (mirab_levelGroups _ _) hSq hY tU hN) hBS (leafUnip_of O D.R.f (mirab_levelGroups _ _) hSq tU hN)
    hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1

end GlobalTheory.OnAtPlacesBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDeterminantOpenImageStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_determinant_open_image : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ U ∈ 𝓝 (1 : UA σ G.W.J), ∃ V ∈ 𝓝 (1 : (Fv F v)ˣ), ∀ x ∈ V,
      ∃ h ∈ UAt σ G.W (evFin F v), h ∈ U ∧ ((mat h).map (piW t)).det = (x : Fv F v) := by
  first | exact @GlobalTheory.SkewLeviNear.near_one_det | exact GlobalTheory.SkewLeviNear.near_one_det | (intros; apply GlobalTheory.SkewLeviNear.near_one_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePointCongrOneOfInvConjCongr
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth.Cong

theorem count_coe_ne_zero_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {J : Ideal (𝓞 E)}
    (hJ : J ≠ ⊥) : FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 ↔ J ≤ w.asIdeal := by
  rw [FractionalIdeal.count_coe E w hJ, Nat.cast_ne_zero, Associates.count_ne_zero_iff_dvd hJ w.irreducible,
    Ideal.dvd_iff_le]

theorem val_le_one_of_mul_eq_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) K) (hHG : H * G = 1) (hH : ∀ i j, v ((1 - H) i j) < 1) (i j : Fin n) : v (G i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun k => v (G k j)) ⟨i, Finset.mem_univ _⟩
  refine (hp i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : v (G p j) ≠ 0 := (zero_lt_one.trans hlt).ne'
  have e : G = 1 + (1 - H) * G := by rw [sub_mul, hHG, one_mul]; abel
  have e2 : G p j = (1 : Matrix (Fin n) (Fin n) K) p j + ∑ k, (1 - H) p k * G k j := by
    conv_lhs => rw [e]
    rw [Matrix.add_apply, Matrix.mul_apply]
  have h1 : v ((1 : Matrix (Fin n) (Fin n) K) p j) < v (G p j) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : v (∑ k, (1 - H) p k * G k j) < v (G p j) := by
    refine v.map_sum_lt h0 fun k _ => ?_
    rw [map_mul]
    calc v ((1 - H) p k) * v (G k j) ≤ v ((1 - H) p k) * v (G p j) := by
          gcongr; exact hp k (Finset.mem_univ _)
      _ < 1 * v (G p j) := mul_lt_mul_of_pos_right (hH p k) (zero_lt_one.trans hlt)
      _ = _ := one_mul _
  have := v.map_add_lt h1 h2
  rw [← e2] at this
  exact lt_irrefl _ this

variable {D : D7}

def evAt (w : HeightOneSpectrum (𝓞 D.host.E)) : FA D →+* w.adicCompletion D.host.E where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem inv_apply {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (i j : Fin n) :
    (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j =
      Formalism.MainNotions.StandardLatticesGL3.sgA D (((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) j i) := by
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * y.1 = 1 := by
    have h2 := y.2
    change Formalism.UG.cT _ (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_left hh]
  rfl

theorem finMat_inv_mul {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : finMat y⁻¹ * finMat y = 1 := by
  unfold finMat
  have := (Matrix.map_mul (f := GlobalTheory.BotFormula.toFinE D)
    (L := (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (M := ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))).symm
  rw [this, Subgroup.coe_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem val_one_le {n : ℕ} (i j : Fin n) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v ((1 : Matrix (Fin n) (Fin n) (FA D)) i j w) ≤ 1 := by
  change Valued.v (evAt w ((1 : Matrix (Fin n) (Fin n) (FA D)) i j)) ≤ 1
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem val_sub_le {x y : FA D} {w : HeightOneSpectrum (𝓞 D.host.E)} (hx : Valued.v (x w) ≤ 1) (hy : Valued.v (y w) ≤ 1) :
    Valued.v ((x - y) w) ≤ 1 := by
  change Valued.v (evAt w (x - y)) ≤ 1
  rw [map_sub]
  exact (Valued.v.map_sub _ _).trans (max_le hx hy)

theorem integral_of_cong {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : ∀ i j, Valued.v ((1 - finMat y⁻¹) i j w) < 1) (i j : Fin n) :
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  constructor
  · refine val_le_one_of_mul_eq_one Valued.v ((finMat y).map (evAt w)) ((finMat y⁻¹).map (evAt w)) ?_ (fun a b => ?_) i j
    · rw [← Matrix.map_mul, finMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have : (1 - (finMat y⁻¹).map (evAt w)) a b = evAt w ((1 - finMat y⁻¹) a b) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [this]; exact h a b
  · have : finMat y⁻¹ i j = (1 : Matrix (Fin n) (Fin n) (FA D)) i j - (1 - finMat y⁻¹) i j := by
      rw [Matrix.sub_apply, sub_sub_cancel]
    rw [this]
    exact val_sub_le (val_one_le i j w) (h i j).le

theorem inHat_of_inv_cong : ∀ {D : D7}, (∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w') →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1) →
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
    Valued.v ((1 - finMat y⁻¹) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)))) →
  ∀ i j, InHat 1 (finMat y i j) ∧ InHat 1 (finMat y⁻¹ i j) ∧
    InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ((finMat y - 1) i j) := by
  intro D hc 𝔪 Sf hG n y hoff hcong
  obtain ⟨h0, hsup, -, hS⟩ := hG
  have h0' : D.host.conj • 𝔪 ≠ ⊥ := fun h => h0 (by
    have := congrArg (fun I => D.host.conj⁻¹ • I) h
    simpa using this)
  have hb : ∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
      Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
    intro w hw
    refine integral_of_cong y w fun i j => (hcong w hw i j).trans_lt ?_
    have h1 := (count_coe_ne_zero_iff w h0').2 hw
    have h2 := FractionalIdeal.count_coe_nonneg D.host.E w (D.host.conj • 𝔪)
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∀ i j, Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 ∧
      Valued.v ((finMat y - 1) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
        (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))) := by
    intro w i j
    by_cases hw : 𝔪 ≤ w.asIdeal
    · obtain ⟨w', e', hv, hcnt, -⟩ := hc w
      have hw' : D.host.conj • 𝔪 ≤ w'.asIdeal := by
        rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw
      have t : ∀ (z : Formalism.MainNotions.StandardLatticesGL3.GA D n) (a b : Fin n), Valued.v (finMat z a b w) = Valued.v (finMat z⁻¹ b a w') := by
        intro z a b
        unfold finMat
        rw [Matrix.map_apply, Matrix.map_apply, inv_apply, hv]
      refine ⟨(t y i j).trans_le (hb w' hw' j i).2, (t y⁻¹ i j).trans_le (by rw [inv_inv]; exact (hb w' hw' j i).1), ?_⟩
      rw [← hcnt 𝔪 h0]
      refine le_of_eq_of_le ?_ (hcong w' hw' j i)
      have e1 : (finMat y - 1) i j = GlobalTheory.BotFormula.toFinE D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      have e2 : (1 - finMat y⁻¹) j i = -GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j)) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub, Matrix.map_apply, inv_apply, neg_sub, Matrix.one_apply,
          Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (Ne.symm hij)]; simp
      rw [e1, e2, ← hv]
      exact (Valuation.map_neg _ _).symm
    · have hint : Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
        by_cases hu : w.under (𝓞 D.host.F) ∈ Sf
        · obtain ⟨w₀, hw₀, e₀⟩ := (hS _).1 hu
          obtain ⟨w', e', -, -, hun⟩ := hc w₀
          rcases (hun w).1 e₀.symm with rfl | rfl
          · exact absurd hw₀ hw
          · exact hb _ (by rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw₀) i j
        · exact hoff w hu i j
      refine ⟨hint.1, hint.2, ?_⟩
      have hz : FractionalIdeal.count D.host.E w (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
        by_contra h; exact hw ((count_coe_ne_zero_iff w h0).1 h)
      rw [hz, neg_zero, WithZero.exp_zero, Matrix.sub_apply]
      exact val_sub_le hint.1 (val_one_le i j w)
  exact fun i j => ⟨(inHat_one_iff _).2 fun w => (key w i j).1, (inHat_one_iff _).2 fun w => (key w i j).2.1,
    fun w => (key w i j).2.2⟩

end GlobalTheory.CosetOrth.Cong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProd
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.NormSum.VacInt.PartFin

open GlobalTheory.NormSum.VacInt

section Cut

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem cutM_of_eq_zero (e : R) (he : e * e = e) (h : e = 0) (A : Matrix n n R) : cutM e he A = 1 := by
  subst h
  show (0 : R) • A + (1 - 0 : R) • (1 : Matrix n n R) = 1
  simp

theorem cutM_add (e e' f : R) (he : e * e = e) (he' : e' * e' = e') (hf : f * f = f) (h0 : e * e' = 0)
    (h : f = e + e') (A : Matrix n n R) : cutM f hf A = cutM e he A * cutM e' he' A := by
  subst h
  have h1 : e * (1 - e') = e := by linear_combination - h0
  have h2 : (1 - e) * e' = e' := by linear_combination - h0
  have h3 : (1 - e) * (1 - e') = 1 - (e + e') := by linear_combination h0
  show (e + e') • A + (1 - (e + e')) • (1 : Matrix n n R) =
    (e • A + (1 - e) • (1 : Matrix n n R)) * (e' • A + (1 - e') • (1 : Matrix n n R))
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, h0, h1, h2, h3,
    zero_smul, zero_add, add_smul]
  abel

end Cut

variable {E : Type} [Field E] [NumberField E]

theorem eps_empty : eps E (fun p => p ∈ (∅ : Finset ℕ)) = 0 :=
  ext_prV fun v => by rw [prV_eps, map_zero]; simp

theorem eps_insert (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p ∈ insert q s) = eps E (fun p => p = q) + eps E (fun p => p ∈ s) :=
  ext_prV fun v => by
    rw [map_add, prV_eps, prV_eps, prV_eps]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · by_cases h2 : pr v ∈ s <;> simp [h1, h2]

theorem eps_single_mul (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p = q) * eps E (fun p => p ∈ s) = 0 :=
  ext_prV fun v => by
    rw [map_mul, prV_eps, prV_eps, map_zero]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · simp [h1]

theorem part_finset : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  intro D N y
  exact ⟨Subtype.ext (Units.ext (cutM_of_eq_zero _ _ eps_empty _)), fun q s h =>
    Subtype.ext (Units.ext (cutM_add _ _ _ _ _ _ (eps_single_mul q s h) (eps_insert q s h) _))⟩

end GlobalTheory.NormSum.VacInt.PartFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | exact GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | (intros; apply GlobalTheory.InertSph.acts_vacCond_of_mem_KAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumSecond
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

theorem supPetersson_of_tamagawa : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) → ∀ P ∈ holSub (U σ).X la, supE (U σ).X la P ^ 2 ≤ ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := fun hT =>
  GlobalTheory.T.weighted_frame_sum_positive (GlobalTheory.T.mass_bound_of_tamagawa_unitary hT) GlobalTheory.T.normOneTorusClassNumberBound_proof

end GlobalTheory
end

