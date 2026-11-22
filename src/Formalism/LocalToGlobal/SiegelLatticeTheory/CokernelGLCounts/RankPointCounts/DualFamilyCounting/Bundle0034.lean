import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0021

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueInlInl
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluedFormOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem form_U_orth {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {u z : V} (hu : u ∈ U)
    (hz : z ∈ orthK h U) : h u z = 0 := by
  have hz' : z ∈ ⨅ w ∈ U, LinearMap.ker (h w) := hz
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hz'
  exact hz' u hu

theorem form_orth_U {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V} {u z : V}
    (hu : u ∈ U) (hz : z ∈ orthK h U) : h z u = 0 :=
  hs.eq_iff.1 (form_U_orth hu hz)

theorem glue_inl_inl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hbo : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hwW : ∀ j, w j ∈ orthK h U) (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0)
    (hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) {i i' : Fin n} (hii : i ≠ i') :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i')) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1 h2 h2
  · exact hbo _ _ hii
  · simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _)]
  · simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_orth_U hs (hbU i') (hwW _)]
  · have hτ' : τ i ≠ τ i' := fun e => hii (hτ i i' h1 h2 e)
    simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _),
      form_orth_U hs (hbU i') (hwW _), hwo _ _ hτ']

theorem glue_inl_w {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hwW : ∀ j, w j ∈ orthK h U)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) {i : Fin n} {j : Fin m}
    (hj : vF 𝔭 (a i) ≠ 0 → τ i ≠ j) :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (w j) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1
  · exact form_U_orth (hbU i) (hwW j)
  · simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, form_U_orth (hbU i) (hwW j), hwo _ _ (hj h1)]

end Formalism.L2.SG.Pf.GluedFormOrthogonality
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem jι_eq' (t : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  have e := UnimodularLocalization.algebraMap_smul_K (K := K) t (1 : K)
  rwa [Algebra.smul_def, mul_one, mul_one] at e

theorem inP_of_mem_pow {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {t : 𝓞 F} (ht : t ∈ 𝔭 ^ k) :
    InP 𝔭 k (algebraMap F K (t : F)) := by
  rw [← jι_eq']
  apply inP_jK
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ht

theorem inP_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ≠ 0) :
    InP 𝔭 (vF 𝔭 t) (algebraMap F K (t : F)) := by
  have := h𝔭.isPrime
  exact inP_of_mem_pow ((G1.mem_pow_iff h𝔭 ht _).2 le_rfl)

theorem mem_SP_of_inP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {k : ℕ}
    {x : K} (hx : InP 𝔭 k x) : (algebraMap F K (π : F))⁻¹ ^ k * x ∈ SP K 𝔭 := by
  obtain ⟨s, hs, rfl⟩ := (mem_noncompactPart_iff hu k x).1 hx
  have h0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  rw [jι_eq', ← mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_mul]
  exact hs

theorem star_fix (hF : IsFixF K F) (x : F) : star (algebraMap F K x) = algebraMap F K x :=
  (hF _).2 ⟨x, rfl⟩

theorem star_inv_pow (hF : IsFixF K F) (x : F) (k : ℕ) :
    star ((algebraMap F K x)⁻¹ ^ k) = (algebraMap F K x)⁻¹ ^ k := by
  rw [← map_inv₀, ← map_pow]; exact star_fix hF _

theorem form_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h (r • x) y = star r * h x y := by
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem form_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h x (r • y) = r * h x y := by
  rw [map_smul, smul_eq_mul]

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (r r' : K) (x y : V) :
    h (r • x) (r' • y) = star r * r' * h x y := by
  rw [form_smul_left, form_smul_right]; ring

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MmIntOfEZ
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmInt_of_EZ {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hR : IsRowReps D F0 what₂)
    {Z : MatZ D} {F' : LFlag (VS D) D.R.rS (Tn u')} (hz : F'.zt = F'.fl.z) (hZ : ZhatL (lf D F0) F' = Z)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z)) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : IsRowLat D F0 Λ) (hE : F' ∈ EZ (Tn u') F0 Λ Z) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') := by
  have hG := (((mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR Z F' hz hZ hP).2 Λ).mp ⟨hΛ, hE⟩
  by_contra hI
  rw [Formalism.L2.SG.Pf.Asm.glueSet_eq_empty (U := UPair D F0 F') hI] at hG
  exact hG

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCR
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RefNBox : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word),
    (Measure.pi (refNX X u)) (LsNc5.boxN X w) =
      ENNReal.ofReal ((Tw w)⁻¹ ^ (D.R.rS * Fintype.card (InfinitePlace X.B.I.F)) *
        (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * D.R.k + D.R.rS ^ 2)))

theorem refNX_haar {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) :
    IsHaarOnSet X.B.I (X.NinfU w) (Measure.pi (refNX X u)) := by
  have hR := fun v : InfinitePlace X.B.I.F => refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v)
    (X.wfr u v) (ProductExactness.zV X u v) (ProductExactness.zV X w v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v)
    (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X w v)
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v => (hR v).1
  have hco : X.NinfU w = (ProductExactness.NinfG X w : Set X.B.I.Ginf) := (ProductExactness.NinfG_coe X w).symm
  refine ⟨inferInstance, ProductExactness.PiM.pi_ne_zero _ fun v => (hR v).2.1, ?_, ?_⟩
  · rw [hco, ProductExactness.NinfG, Subgroup.coe_pi]
    exact ProductExactness.PiM.pi_conc _ _ fun v => (hR v).2.2.1
  · intro g hg
    rw [hco] at hg
    exact ProductExactness.PiM.pi_map_mul_left _ g fun v => (hR v).2.2.2 (g v) (hg v (Set.mem_univ v))

theorem covol_refN (hN : LsNc5.CovolN) (hB : RefNBox) {D : D7} (X : HidaSetting D) (u w : D.what₂.Word)
    (FdN : Set X.B.I.Ginf) (hF : IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X w) FdN) :
    ((Measure.pi (refNX X u)) FdN).toReal = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent D.R.rS D.R.k := by
  rw [hN D X w _ FdN (refNX_haar X u w) hF, hB X u w]
  set f := Fintype.card (InfinitePlace X.B.I.F) with hf
  set r := D.R.rS with hr
  set k := D.R.k with hk
  have hT : 0 < Tw (D := D) w := ProductExactness.Tw_pos w
  have hd : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have h2r : 2 * (r * (r - 1) / 2) + 2 * (r * (r + 1) / 2) = 2 * r ^ 2 := by
    have e1 : 2 * (r * (r - 1) / 2) = r * (r - 1) := Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
    have e2 : 2 * (r * (r + 1) / 2) = r * (r + 1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self r).two_dvd
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      ring
  have hsum : r * (r - 1) / 2 + r * (r + 1) / 2 = r ^ 2 := by omega
  unfold LsNc5.covolN
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [show ((D.mem w).A.T : ℕ) = Tw (D := D) w from rfl]
  have hpow : (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
      (2 : ℝ) ^ (f * (r * k + r ^ 2)) = 1 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← hsum]
    rw [show f * (r * k + (r * (r - 1) / 2 + r * (r + 1) / 2)) =
      f * (r * k + r * (r - 1) / 2) + f * (r * (r + 1) / 2) by ring, pow_add]
    have h1 : (0 : ℝ) < 2 ^ (f * (r * k + r * (r - 1) / 2)) := by positivity
    have h2 : (0 : ℝ) < 2 ^ (f * (r * (r + 1) / 2)) := by positivity
    field_simp
  have hTp : (Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hT.ne', one_pow]
  calc (Tw (D := D) w : ℝ) ^ (r * f) * (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
        ((Tw (D := D) w)⁻¹ ^ (r * f) * (2 : ℝ) ^ (f * (r * k + r ^ 2)))
      = ((Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f)) *
        ((2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
          (2 : ℝ) ^ (f * (r * k + r ^ 2))) * |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by ring
    _ = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by rw [hTp, hpow, one_mul, one_mul]

theorem covolRef_of (hN : LsNc5.CovolN) (hB : RefNBox) : CovolRef := by
  delta CovolRef
  intro D X hb FdN FdN' u u' hH
  have hd : (0 : ℝ) < |(NumberField.discr X.B.I.F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  rw [covol_refN hN hB X u _ FdN hH.2.2.1,
    covol_refN hN hB X u _ FdN' (by first | exact hH.2.2.2.1 | exact hH.2.2.2), ← Real.rpow_add hd]
  congr 1
  delta eDF LsNc5.covolumeExponent
  ring

theorem covolRef_of_steps (hC : LsNc5.CoordCovol) (hB : RefNBox) : CovolRef :=
  covolRef_of (covolN_of_coordCovol hC) hB

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrd
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sdNormDV_of {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (hA : AnnX X ψ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : SdNormDV X ψ := by
  have c1 : SdFromAnn := SdW.sdFromAnn_holds
  intro v hv ι _
  refine c1 ψ v (dV v) hψ ?_ ?_ (hA hψ hs v) ι
  · exact X.B.I.cm.deg2
  · exact VolOrdW.dV_ne_zero (v := v)

theorem volOrdV_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hC : CondAll) : VolOrdV X u u' ψ := by
  intro hψ hs
  exact volOrd_body X u u' ψ (sdNormDV_of X ψ (annX_of X ψ hC) hψ hs) SdW.boxScaleL_holds

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem unramAt_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) : UnramAt (E := E) v := by
  intro P hP hP0 _
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  let c : Gal(E/F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => (hc.fixed (algebraMap F E r)).2 ⟨r, rfl⟩)
  haveI : P.LiesOver (P.under (𝓞 F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 F) hP0
  have hcard : Nat.card (P.inertia Gal(E/F)) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) (P.under (𝓞 F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P Gal(E/F)]
  by_contra hne
  have hG : Nat.card Gal(E/F) = 2 := by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hc.deg2)
      | (rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]; exact hc.deg2)
  haveI : Fact (Nat.card Gal(E/F)).Prime := ⟨by rw [hG]; exact Nat.prime_two⟩
  have htop : P.inertia Gal(E/F) = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (P.inertia Gal(E/F)) with h | h
    · exfalso
      apply hne
      rw [← hcard, h]
      simp
    · exact h
  have hcI : c ∈ P.inertia Gal(E/F) := htop ▸ Subgroup.mem_top c
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P (hP.isMaximal hP0)
  apply hθ
  have h1 := hcI θ
  have e : c • θ = t := by
    apply RingOfIntegers.coe_injective
    rw [ht]
    rfl
  rw [e] at h1
  have : θ - t = -(t - θ) := by ring
  rw [this]
  exact P.neg_mem h1

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omega_standard_holds : OmVStd X ψ := by
  intro h1 h2
  refine ⟨?_, ?_, h1, h2⟩
  · unfold IsCMExt
    refine ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, ?_⟩
    exact fun τ x => X.B.I.cm.cmUnram.2.1 τ x
  · unfold IsHermND
    have hH := X.B.I.J_herm
    unfold Formalism.UG.IsHerm at hH
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have h3 := congrFun (congrFun hH i) j
    exact h3

theorem omega_lattice_holds : OmVLat X := ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩

theorem omega_unramified_holds : OmVUnram X := fun v => unramAt_of_cm X.B.I.cm v

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL
section
noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

theorem det_LyM {r k : ℕ} {T : ℝ} (hT : 0 < T) : LinearMap.det (LyM (k := k) (r := r) T) = T ^ r := by
  rw [LyM, LinearMap.det_toLin', Matrix.det_diagonal]
  simp only [Fintype.prod_sum_type, dY, Finset.prod_const_one, one_mul, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [show r * 2 = 2 * r by ring, pow_mul, Real.sq_sqrt hT.le]

theorem refN_map_kapL {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    AEMeasurable (kapL ε e f w z) (refNg hn ε e f w (z0v T z)) ∧
      (refNg hn ε e f w (z0v T z)).map (kapL ε e f w z) =
        ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k) * (T ^ r)⁻¹) • volume := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  let ψ : Mt k r → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun x => (WlocSk.NB.psiC x, WlocSk.NB.psiR x)
  have hψc : Continuous ψ := WlocSk.NB.continuous_psiC.prodMk WlocSk.NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := fun t => by
    obtain ⟨h1, h2⟩ := WlocSk.NB.nilpotent_chart_right_inverse t.1 t.2
    show (WlocSk.NB.psiC (WlocSk.NB.phi0 t.1 t.2), WlocSk.NB.psiR (WlocSk.NB.phi0 t.1 t.2)) = t
    rw [h1, h2]
  have hΦe : MeasurableEmbedding Φ := by
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have hr : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [hr]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  set ν := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map Φ with hν
  haveI : SigmaFinite ν := hΦe.sigmaFinite_map
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [hν, Measure.map_eq_zero_iff hΦe.measurable.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))) Set.univ_nonempty
      (by rw [h0, Measure.coe_zero, Pi.zero_apply])
  have hrange : ∀ t, ∃ g : Formalism.REAL.UJ ε, Ψ g = Φ t := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  set lam0 := Measure.comap Ψ ν with hlam0
  have hmap : lam0.map Ψ = ν := by
    rw [hlam0, emb.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, hν, hΦe.map_apply]
    convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨g, hg⟩ := hrange t
    exact ⟨g, hg⟩
  haveI : SigmaFinite lam0 := SigmaFinite.of_map _ emb.measurable.aemeasurable (by rw [hmap]; infer_instance)
  have hNz : NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) = NLoc ε e z := by rw [hQz]
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  have hHaar : IsHaarLoc (NLoc ε e z) lam0 := by
    refine ⟨inferInstance, fun h0 => hν0 (by rw [← hmap, h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
    · rw [hlam0, emb.comap_apply, hν, hΦe.map_apply]
      convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
      ext t
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_exists, not_and]
      intro g hg hgt
      apply hg
      rw [← hNz]
      refine inN_of_conj hFJ (inWb_zB T) ?_
      have : (Qi ε e f w (z0v T z) * uMat g * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2 := hgt
      rw [this]; exact hΦN t
    · have hs' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat s) := by
        have h1 : s ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hs
        exact h1
      have h0 : Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) ∈ Nset k r :=
        conj_mem_Nset hFJ hz0 (uMat_mem s) hs'
      set m0 := Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) with hm0
      have hfun : Ψ ∘ (fun x => s * x) = lmulM m0 ∘ Ψ := by
        funext x
        show (Qi ε e f w (z0v T z) * uMat (s * x) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
          m0 * (Qi ε e f w (z0v T z) * uMat x * Qm e f w (z0v T z))
        rw [uMat_mul, hm0]
        simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (Qi ε e f w (z0v T z) * uMat s) (Qm e f w (z0v T z)) (Qi ε e f w (z0v T z)),
          Qm_mul_Qi hFJ, Matrix.mul_one]
      have hsh : lmulM m0 ∘ Φ = Φ ∘ (fun t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) =>
          (t.1 + WlocSk.NB.shG m0 t.1, t.2 + WlocSk.NB.shH m0 t.1)) := by
        funext t
        obtain ⟨h1, h2⟩ := WlocSk.NB.lmul_coord h0 t.1 t.2
        have hmem := WlocSk.UnitaryGroupBasics.mem_n_mul h0 (WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2)
        show m0 * WlocSk.NB.phi0 t.1 t.2 =
          WlocSk.NB.phi0 (t.1 + WlocSk.NB.shG m0 t.1) (t.2 + WlocSk.NB.shH m0 t.1)
        rw [← h1, ← h2]
        exact (WlocSk.NB.nilpotent_chart_left_inverse hmem).symm
      have hmp := WlocSk.NB.shear_mp (d := r) WlocSk.NB.rk (WlocSk.NB.shG m0) (WlocSk.NB.shH m0)
        (fun i => (WlocSk.NB.continuous_shG m0 i).measurable) (fun i x y h => WlocSk.NB.shG_dep m0 i x y h)
        (WlocSk.NB.continuous_shH m0).measurable
      have key : (lam0.map (fun x => s * x)).map Ψ = lam0.map Ψ := by
        rw [Measure.map_map emb.measurable (measurable_const_mul s), hfun,
          ← Measure.map_map (measurable_lmulM m0) emb.measurable, hmap, hν,
          Measure.map_map (measurable_lmulM m0) hΦe.measurable, hsh,
          ← Measure.map_map hΦe.measurable hmp.measurable, hmp.map_eq]
      rw [← emb.comap_map (lam0.map (fun x => s * x)), key, emb.comap_map]
  have hkc : ∀ᵐ g ∂lam0, kapL ε e f w z g = (Kc T ∘ Ψ) g := by
    filter_upwards [(ae_iff.2 hHaar.2.2.1 : ∀ᵐ g ∂lam0, g ∈ NLoc ε e z)] with g hg
    have hg' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat g) := by
      have h1 : g ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hg
      exact h1
    exact kapL_eq hFJ hT g (conj_mem_Nset hFJ hz0 (uMat_mem g) hg')
  have hdet := det_LyM_ne (k := k) (r := r) hT
  set c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (LyM (k := k) (r := r) T))⁻¹| with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeasK : AEMeasurable (kapL ε e f w z) lam0 :=
    ((Kc_cont T).measurable.comp emb.measurable).aemeasurable.congr (Filter.EventuallyEq.symm hkc)
  have hcomp : Kc T ∘ Φ = LyM (k := k) (r := r) T ∘ Rc := by
    funext t
    funext i
    rw [Function.comp_apply, Function.comp_apply, LyM_apply]
    exact chart_kappa_coordinates T t i
  have hH : Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • ν := by
    rw [hν]
    exact exponential_chart_haar k r
  have hrefN : refNg rfl ε e f w (z0v T z) = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • lam0 := by
    rw [refNg_rfl]
    ext s _
    show (Measure.comap Ψ (Formalism.MainNotions.S.haarLie (Nset k r) 1)) s = _
    rw [emb.comap_apply, hH, Measure.smul_apply, Measure.smul_apply, hlam0, emb.comap_apply]
  have hlamK : lam0.map (kapL ε e f w z) = c • volume := by
    rw [Measure.map_congr hkc, ← Measure.map_map (Kc_cont T).measurable emb.measurable, hmap, hν,
      Measure.map_map (Kc_cont T).measurable hΦe.measurable, hcomp,
      ← Measure.map_map (LyM (k := k) (r := r) T).continuous_of_finiteDimensional.measurable Rc_cont.measurable,
      map_Rc, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, ← hc]
  refine ⟨?_, ?_⟩
  · rw [hrefN]
    exact hmeasK.smul_measure _
  · rw [hrefN, Measure.map_smul, hlamK, smul_smul, hc, det_LyM hT, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [abs_of_pos (by positivity)]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

