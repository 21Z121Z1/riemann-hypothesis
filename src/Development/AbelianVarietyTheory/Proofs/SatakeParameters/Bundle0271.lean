import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatticeSmulMemOfAgreeAwayFromPlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0264
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumRationalTranslatesVsClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem inFr_inFr_eq_toLin {E : Type} [Field E] {a b : ℕ} (f g : Sp E a ≃ₗ[E] Sp E a) (f' g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Matrix (Fin b) (Fin b) E) (hN : LinearMap.toMatrix' (f'.trans g').toLinearMap * N = 1) (z : HomE E a b) :
    inFr f f' (inFr g g' z) = Matrix.toLin' N ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' (f.trans g).toLinearMap) := by
  rw [Matrix.toLin'_toMatrix']
  have key : ∀ y, Matrix.toLin' N y = (f'.trans g').symm y := by
    intro y
    have h : (f'.trans g') (Matrix.toLin' N y) = y := by
      have h0 := congrArg (fun M => Matrix.toLin' M y) hN
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix'] at h0
      exact h0
    exact ((f'.trans g').symm_apply_eq.2 h.symm).symm
  ext w l
  simp only [inFr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]

set_option maxHeartbeats 1000000 in
theorem adelicDatum_at_translates : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) = 1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x' z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * (t.rd u μ).Xi i c c' (seamHom t.seam (Matrix.toLin' (star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap)) ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap)))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hM z
  have hr : ratA D.host.F γ ∈ UPts (sigD D) (gramN D i (Nat.le_of_succ_le hi)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ, hγ, rfl⟩
  have hr' : ratA D.host.F γ' ∈ UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ', hγ', rfl⟩
  let x₀ : UA D i (Nat.le_of_succ_le hi) := ⟨ratA D.host.F γ * ((St i _).y c).1, mul_mem hr ((St i _).y c).2⟩
  let x₀' : UA D (i + 1) hi := ⟨ratA D.host.F γ' * ((St (i + 1) hi).y c').1, mul_mem hr' ((St (i + 1) hi).y c').2⟩
  have h1 := law.lev i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') x₀ x₀' x x' κ κ' hx hx' z
  have h2 := law.rat i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') ((St i _).y c) ((St (i + 1) hi).y c') x₀ x₀' γ hγ γ' hγ' rfl rfl z
  have h3 := law.read i hi c c' (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)
  refine h1.trans ?_
  rw [h2, h3, inFr_inFr_eq_toLin _ _ _ _ _ hM z]

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicFiniteDatumIntegralOffBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV.AdInt

theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem intOff_of_isIntegral {K : Type} [Field K] (σ : K →+* ℂ) (S : Finset ℕ) {x : K} (hx : IsIntegral ℤ x) :
    IntOff S (σ x) := by
  have hx' : IsIntegral ℤ (σ x) := map_isIntegral_int σ hx
  have h : σ x ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff'.2 hx'.tower_top
  refine ⟨h, fun p _ lam _ => ?_⟩
  rw [lamC_of_mem lam h]
  have h1 : IsIntegral ℤ (⟨σ x, h⟩ : TaylorLogMetric.Qbar) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx'
  exact norm_le_one_of_isIntegral' (map_isIntegral_int lam h1)

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV.AdInt

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff_of_psi (P : rowSG Pr sel mu) (hpsi : ∀ a, IsIntegral ℤ (cst.psi P a)) (σ : X.K →+* ℂ) {B : Finset ℕ}
    (hB : SNum B (qOf P.1)) {n : ℕ} (η : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  unfold ftY
  split_ifs
  · exact intOff_of_isIntegral σ B (hpsi _)
  · simpa using (IntOff.zero : IntOff B 0)
  · rw [map_mul, map_inv₀, map_pow, map_natCast]
    refine IntOff.mul ?_ (intOff_of_isIntegral σ B (hpsi _))
    have hB' : SNum B (qOf P.1 ^ (cst.M * n)) :=
      ⟨pow_pos hB.1 _, fun q hq hd => hB.2 q hq (hq.dvd_of_dvd_pow hd)⟩
    simpa [Nat.cast_pow] using IntOff.inv_nat hB'
  · simpa using (IntOff.zero : IntOff B 0)

end Ft

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX}

theorem xiTop_intOff_of_psi (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hpsi : ∀ P x, IsIntegral ℤ ((t.cst μ).psi P x)) (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i)
    (Yb : Set (Sp t.X.E (D.R.N i))) (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1))
    (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) :
    IntOff (t.O u μ).S (t.seam.σ₀ (XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  unfold XiTop XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (GlobalTheory.intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((GlobalTheory.TopInt.phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff_of_psi t.sel (t.tup μ) (t.cst μ) P (hpsi P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl Kc Y cX ex t u μ P) _ _

theorem plc_dvd_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

theorem g_not_mem_Qp (t : KerEntTied ex) (hsel : IsSel t.X t.sel) (hg : ∀ k, t.Pr.g k ∈ t.S) (μ : D.what₂.Tup) (k : Fin 2) :
    D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg'
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg'
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hsel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hg k
  · simp at hPQ

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV

theorem xiAd_intOff : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → ∀ i hi β β' x x' z,
    IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ _ i hi β β' x x' z
  have hmu : ∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j) := fun j => ⟨_, hP.mu0 j⟩
  have hval : ∀ (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) →
      t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ) := fun j v hv => by
    have h := hP.ch.muVal j v hv
    rwa [t.glob_σ] at h
  have hg : ∀ k, D.host.g k ∉ Y.Qp μ := AdInt.g_not_mem_Qp t hP.sel hP.avoid.1 μ
  unfold xiAd
  split_ifs with h
  · unfold xiPt
    split_ifs with h1 h2
    · exact GlobalTheory.KerTie.intOff_xiEntry D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg i h1 _ _ _ _ _
    · subst h2
      exact GlobalTheory.xiCpl1_intOff D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg _ _ _ _ _
    · exact AdInt.xiTop_intOff_of_psi t u μ hP.psi _ _ _ _ _
  · exact IntOff.zero

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatticeSmulMemOfAgreeAwayFromPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_smul_mem_of_agree_away_from_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (w : HeightOneSpectrum (𝓞 F)) (x x' : GL (Fin N) (AfE F E)), SameOff w x x' → ∃ m : ℕ, ∀ c : 𝓞 F, c ∈ w.asIdeal ^ m → ∀ y ∈ latAd x Lb, (algebraMap F E (c : F)) • y ∈ latAd x' Lb := by
  first | exact @GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff | exact GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff | (intros; apply GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixOneAtPlaceScaledPreservesCompletedLa
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.AwayScale
variable {F : Type} [Field F] [NumberField F]

theorem scalar (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (ha : a v = 0) (M : ℕ) (hM : 0 < M) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∃ y ∈ Formalism.UG.intAd F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) * a =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F) * y := by
  classical
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.Idele.exists_mul_integral a
  set c : 𝓞 F := b * (M : 𝓞 F) with hc
  have hc0 : c ≠ 0 := mul_ne_zero hb0 (by exact_mod_cast hM.ne')
  have hfin : {w : HeightOneSpectrum (𝓞 F) | w.asIdeal ∣ Ideal.span {c}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hc0)
  let e : HeightOneSpectrum (𝓞 F) → ℕ := fun w => if w = v then 1 else
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {c})).factors
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v hfin.toFinset)
    (fun w => w.asIdeal) e (fun w _ => w.prime) (fun w _ w' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then 1 else 0)
  have htv : t ∉ v.asIdeal := by
    intro h
    have h1 := ht v (Finset.mem_insert_self _ _)
    simp only [e, if_true, pow_one] at h1
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : (1 : 𝓞 F) = t - (t - 1) := by ring
    rw [h2]
    exact sub_mem h h1
  have hval : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.intValuation t ≤ w.intValuation c := by
    intro w hw
    by_cases hws : w ∈ hfin.toFinset
    · have h1 := ht w (Finset.mem_insert_of_mem hws)
      simp only [hw, if_false, sub_zero, e] at h1
      rw [w.intValuation_if_neg hc0]
      exact (w.intValuation_le_pow_iff_mem t _).2 h1
    · have h1 : c ∉ w.asIdeal := by
        intro h; apply hws
        rw [Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.2 h
      rw [(w.intValuation_eq_one_iff_mem_primeCompl c).2 h1]
      exact w.intValuation_le_one t
  have hcF : algebraMap (𝓞 F) F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact hc0
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact hb0
  have hMF : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨t, htv, algebraMap F _ (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F c) *
    (algebraMap F _ (algebraMap (𝓞 F) F b) * a), ?_, ?_⟩
  · intro w
    show (algebraMap F _ (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F c) *
      (algebraMap F _ (algebraMap (𝓞 F) F b) * a)) w ∈ w.adicCompletionIntegers F
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.Idele.adele_mul_apply, GlobalTheory.Idele.adele_mul_apply, ha, mul_zero, mul_zero]
      exact zero_mem _
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.adele_mul_apply, map_mul]
      refine mul_le_one' ?_ (hb w)
      rw [GlobalTheory.Idele.adele_algebraMap_apply, GlobalTheory.Idele.valued_algebraMap, map_div₀,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      rw [div_le_one₀ (by rw [pos_iff_ne_zero]; exact w.intValuation_ne_zero c hc0)]
      exact hval w hw
  · rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 2
    rw [hc, map_mul, map_natCast]
    field_simp

theorem algebraMap_mem_intAd (r : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) ∈ Formalism.UG.intAd F := by
  intro w
  show algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) w ∈ w.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.adele_algebraMap_apply,
    GlobalTheory.Idele.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact w.intValuation_le_one r

theorem scalarFam (v : HeightOneSpectrum (𝓞 F)) {ι : Type} [Fintype ι] (a : ι → FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ i, a i v = 0) (M : ℕ) (hM : 0 < M) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ i, ∃ y ∈ Formalism.UG.intAd F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) * a i =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F) * y := by
  classical
  choose t ht y hy he using fun i => scalar v (a i) (ha i) M hM
  have hT : ∏ i, t i ∈ v.asIdeal.primeCompl := Submonoid.prod_mem _ fun i _ => ht i
  refine ⟨∏ i, t i, hT, fun i => ?_⟩
  refine ⟨algebraMap F _ (algebraMap (𝓞 F) F (∏ j ∈ Finset.univ.erase i, t j)) * y i,
    mul_mem (algebraMap_mem_intAd _) (hy i), ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, map_mul, mul_comm (algebraMap F _ _),
    mul_assoc, he i]
  ring

theorem prV_tmul {E : Type} [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (a : FiniteAdeleRing (𝓞 F) F) : prV (E := E) v (x ⊗ₜ[F] a) = x ⊗ₜ[F] a v := by
  show (Algebra.TensorProduct.map (AlgHom.id F E) (Formalism.UG.evalV F v)) (x ⊗ₜ[F] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem basis_coeff {E N : Type} [Field E] [AddCommGroup N] [Module F N] [Algebra F E] {d : ℕ}
    (bE : Module.Basis (Fin d) F E) (x : Fin d → N) (k : Fin d) :
    TensorProduct.equivFinsuppOfBasisLeft bE (∑ j, bE j ⊗ₜ[F] x j) k = x k := by
  classical
  simp [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

theorem basis_expand {E N : Type} [Field E] [AddCommGroup N] [Module F N] [Algebra F E] {d : ℕ}
    (bE : Module.Basis (Fin d) F E) (z : E ⊗[F] N) :
    z = ∑ j, bE j ⊗ₜ[F] TensorProduct.equivFinsuppOfBasisLeft bE z j := by
  classical
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply bE (TensorProduct.equivFinsuppOfBasisLeft bE z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  exact h

theorem tensorFam {E : Type} [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    {ι : Type} [Fintype ι] (m : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hm : ∀ i, prV (E := E) v (m i) = 0)
    (M : ℕ) (hM : 0 < M) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ i, ∃ y ∈ Formalism.L2.Herm.intAf F E,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) * m i =
        Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (M : E) * y := by
  classical
  let bE := Module.finBasis F E
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatAdelicBasis.exists_nat_multiples (Finset.univ.image bE)
  choose o ho using fun j => hcb (bE j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  let a : ι × Fin (Module.finrank F E) → FiniteAdeleRing (𝓞 F) F :=
    fun p => TensorProduct.equivFinsuppOfBasisLeft bE (m p.1) p.2
  have hexp : ∀ i, m i = ∑ j, bE j ⊗ₜ[F] a (i, j) := fun i => basis_expand bE (m i)
  have ha : ∀ p, a p v = 0 := by
    intro p
    have h := hm p.1
    rw [hexp p.1, map_sum] at h
    simp only [prV_tmul] at h
    have := congrArg (fun z => TensorProduct.equivFinsuppOfBasisLeft bE z p.2) h
    simp only [basis_coeff, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this
  obtain ⟨t, ht, hty⟩ := scalarFam v a ha (M * c) (Nat.mul_pos hM hc0)
  choose y hy he using hty
  refine ⟨t, ht, fun i => ⟨∑ j, (algebraMap (𝓞 E) E (o j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) *
      ((1 : E) ⊗ₜ[F] y (i, j)), ?_, ?_⟩⟩
  · exact sum_mem fun j _ => mul_mem (GlobalTheory.LatAdelicBasis.left_mem F E (o j))
      (GlobalTheory.LatAdelicBasis.right_mem F E (y (i, j)) (hy (i, j)))
  · have htE : ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F t) := rfl
    rw [hexp i, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [htE, ← ho j, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, he (i, j)]
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    rw [Nat.cast_mul, map_mul, map_natCast, map_natCast]
    ring

end GlobalTheory.AwayScale

theorem GlobalTheory.AwayScale.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) k = 1 →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Lb,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) •
        ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  intro F E _ _ _ _ _ N Lb hfg hsp v k hk
  classical
  obtain ⟨n, hn0, hn1, hn2⟩ := GlobalTheory.LatAdelicBasis.exists_level Lb hfg hsp
  let ι := Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  let K : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := (k : Matrix _ _ _)
  let m : Fin N × Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun p => (K - 1) p.1 p.2
  have hK : K.map (prV (E := E) v) = 1 := congrArg Units.val hk
  have hm : ∀ p, prV (E := E) v (m p) = 0 := by
    intro p
    have h1 : (K - 1).map (prV (E := E) v) = 0 := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b), hK, Matrix.map_one _ (map_zero _) (map_one _), sub_self]
    exact congrFun (congrFun h1 p.1) p.2
  obtain ⟨t, ht, hty⟩ := GlobalTheory.AwayScale.tensorFam v m hm (n * n) (Nat.mul_pos hn0 hn0)
  choose y hy he using hty
  refine ⟨t, ht, fun z hz => ?_⟩
  have hι : ∀ o : 𝓞 E, ι (algebraMap (𝓞 E) E o) ∈ Formalism.L2.Herm.intAf F E :=
    fun o => GlobalTheory.LatAdelicBasis.left_mem F E o

  have hZ : ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Lb, ∀ i, ι (n : E) * w i ∈ Formalism.L2.Herm.intAf F E := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      intro i
      obtain ⟨o, ho⟩ := hn2 x hx i
      show ι (n : E) * ι (x i) ∈ _
      rw [← map_mul, ho]
      exact hι o
    | zero => intro i; simp
    | add w w' _ _ hw hw' => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hw i) (hw' i)
    | smul r w _ hw =>
      intro i
      rw [Subring.smul_def, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem r.2 (hw i)

  have hW : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∃ u ∈ Formalism.L2.Herm.intAf F E, w i = ι (n : E) * u) → w ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
    intro w hw
    choose u hu hwu using hw
    have hw' : w = ∑ i, (⟨u i, hu i⟩ : Formalism.L2.Herm.intAf F E) •
        (fun l => ι (((n : E) • (Pi.single i 1 : Fin N → E)) l)) := by
      funext l
      rw [Finset.sum_apply, Finset.sum_eq_single l]
      · rw [Subring.smul_def, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
          hwu l, mul_comm]
      · intro i _ hil
        rw [Subring.smul_def, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hil), smul_zero, map_zero,
          smul_zero]
      · intro h; exact absurd (Finset.mem_univ l) h
    rw [hw']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hn1 i, rfl⟩)
  have htE : ι ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) ∈ Formalism.L2.Herm.intAf F E := hι _
  have hsplit : K *ᵥ z = z + (K - 1) *ᵥ z := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  show ι ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) • (K *ᵥ z) ∈ _
  rw [hsplit, smul_add]
  refine add_mem ?_ ?_
  · have := (Formalism.L2.Herm.hatL (F := F) Lb).smul_mem (⟨_, htE⟩ : Formalism.L2.Herm.intAf F E) hz
    rwa [Subring.smul_def] at this
  · refine hW _ fun i => ?_
    have hent : (ι ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) • ((K - 1) *ᵥ z)) i =
        ι (n : E) * ∑ j, y (i, j) * (ι (n : E) * z j) := by
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 := he (i, j)
      rw [← mul_assoc]
      change ι _ * m (i, j) * z j = _
      rw [h1, Nat.cast_mul, map_mul]
      ring
    exact ⟨_, sum_mem fun j _ => mul_mem (hy (i, j)) (hZ z hz j), hent⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGL
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

theorem mulVec_mem_hatL_mvL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {N : ℕ} (h : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) M) :
    ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
      Formalism.L2.Herm.hatL (F := F) (mvL h M) := by
  unfold Formalism.L2.Herm.hatL latS at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxM, rfl⟩ := hx
    refine Submodule.subset_span ⟨(h : Matrix (Fin N) (Fin N) E) *ᵥ x, ?_, ?_⟩
    · exact ⟨x, hxM, rfl⟩
    · exact (bc_mulVec (F := F) h x).symm
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ s ha

theorem mvL_one_lat {E : Type} [Field E] [NumberField E] {N : ℕ} (M : Submodule (𝓞 E) (Fin N → E)) : mvL 1 M = M := by
  unfold mvL; ext x; simp [toLE_apply]

theorem latAd_mul_ratA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)),
    latAd (y * ratA F g) M = latAd y (mvL g M) := by
  intro F E _ _ _ _ _ _ N y g M
  have key : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      ((ratA F g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
        Formalism.L2.Herm.hatL (F := F) M ↔ w ∈ Formalism.L2.Herm.hatL (F := F) (mvL g M) := by
    intro w
    constructor
    · intro hw
      have := mulVec_mem_hatL_mvL g M _ hw
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec] at this
    · intro hw
      have := mulVec_mem_hatL_mvL g⁻¹ (mvL g M) w hw
      rwa [← mvL_mul, inv_mul_cancel, mvL_one_lat] at this
  unfold latAd
  congr 1
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, key]

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponentStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  first | (exact @GlobalTheory.Cong.span_comp_of_split) | (exact GlobalTheory.Cong.span_comp_of_split) | (intros; apply GlobalTheory.Cong.span_comp_of_split  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawTopLevelStabilizerStatement
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_law_topLevelStabilizer : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → 2 * cst.M ≤ twTopDepth R → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (a : FrmG (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N → a • p' = p' → ∀ x, XiTop Ch sel mu cst (m2 + 1) p Y p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) * XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  first | exact @GlobalTheory.StabTopLaw.xiTop_stab_law | exact GlobalTheory.StabTopLaw.xiTop_stab_law | (intros; apply GlobalTheory.StabTopLaw.xiTop_stab_law <;> assumption)
end

