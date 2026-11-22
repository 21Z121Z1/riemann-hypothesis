import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0468
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem breuilKisinDatum_radius_pow_degree_eq_inv {K : FinExt l} (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem breuilKisinDatum_radius_le_one {K : FinExt l} (bk : BK K) : bk.ρ₀ ≤ 1 := by
  unfold BK.ρ₀
  exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hl.out.one_lt.le)
    (neg_nonpos.2 (by positivity))

theorem breuilKisinDatum_radius_pos {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem inv_le_rho {K : FinExt l} (bk : BK K) {ρ : ℝ≥0} (h : bk.ρ₀ ≤ ρ) : (l : ℝ≥0)⁻¹ ≤ ρ := by
  rw [← breuilKisinDatum_radius_pow_degree_eq_inv]
  exact (pow_le_of_le_one (by positivity) (breuilKisinDatum_radius_le_one bk) bk.deg_pos.ne').trans h

theorem E_eq {K : FinExt l} (bk : BK K) : ∃ q : bk.S, bk.E = X ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hm : bk.Ep - Polynomial.X ^ bk.Ep.natDegree ∈ (Ideal.span {(l : Wq l bk.a)}).map Polynomial.C := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy n bk.Ep.natDegree with hn | hn | hn
    · rw [if_neg hn.ne, sub_zero]
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · subst hn
      rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact zero_mem _
    · rw [if_neg hn.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hn, sub_zero]; exact zero_mem _
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm
  obtain ⟨q, hq⟩ := hm
  refine ⟨(q : bk.S), ?_⟩
  have h1 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  have h2 : (bk.Ep : bk.S) =
      ((Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q : Polynomial (Wq l bk.a)) : bk.S) :=
    congrArg _ h1
  show (bk.Ep : bk.S) = _
  rw [h2, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C, map_natCast]

theorem gauge_mono_le {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : ℕ) {r : ℝ} (hr : 0 < r)
    (h : (ρ : ℝ) ^ b ≤ r * (l : ℝ) ^ a) :
    ‖algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b)‖ ≤ r :=
  gauge_le l u ρ hr (Submodule.subset_span ⟨a, b, 0, by simpa using h, by simp⟩)

end GlobalTheory.BSP.DiscPrism

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_toDisc_hf_le {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0)
    (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ ≤ 1) : ‖toDisc l (BK.hf f X) ρ (BK.hf g X)‖ ≤ ρ := by
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 ((breuilKisinDatum_radius_pos bk).trans_le h0)
  have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast h1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hlρ : (1 : ℝ) ≤ ρ * l := by
    have h := inv_le_rho bk h0
    have h' : ((l : ℝ))⁻¹ ≤ ρ := by exact_mod_cast h
    rw [inv_le_iff_one_le_mul₀ hl0] at h'
    linarith [mul_comm (l : ℝ) ρ]
  set u := BK.hf f X with hu
  let am := algebraMap B.A (PreDisc l u ρ)
  have um : ∀ x y : PreDisc l u ρ, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := gauge_add_le_max l u ρ
  have hX : ‖am u‖ ≤ ρ := by
    simpa using gauge_mono_le (l := l) u ρ 0 1 hρ (by simp)
  have hE : ‖am (BK.hf f bk.E)‖ ≤ ρ := by
    obtain ⟨q, hq⟩ := E_eq bk
    have e1 : BK.hf f bk.E = u ^ bk.Ep.natDegree + (l : B.A) ^ 1 * u ^ 0 * BK.hf f q := by
      rw [hq, map_add, map_pow, map_mul, map_natCast, hu]; ring
    rw [e1, map_add, map_mul]
    refine (um _ _).trans (max_le ?_ ?_)
    · have := gauge_mono_le (l := l) u ρ 0 bk.Ep.natDegree hρ
        (by simpa using pow_le_of_le_one hρ.le hρ1 bk.deg_pos.ne')
      simpa using this
    · refine (norm_mul_le _ _).trans ?_
      have h2 := gauge_mono_le (l := l) u ρ 1 0 hρ (by simpa using hlρ)
      have h3 := norm_algebraMap_le (l := l) (u := u) (ρ := ρ) (BK.hf f q)
      calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul h2 h3 (norm_nonneg _) hρ.le
        _ = ρ := mul_one _
  have hmem : BK.hf g X - BK.hf f X ∈ B.I := by
    have hs : Ideal.Quotient.mk bk.prism.I (X : bk.S) = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ X)) :=
      (bk.str.apply_symm_apply _).symm
    exact Ideal.Quotient.eq.1 ((g.f_str _ _ hs).trans (f.f_str _ _ hs).symm)
  have hI : B.I = Ideal.span {BK.hf f bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l ↥(OL K) bk.prism B f]
    show (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  rw [hI, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have e2 : BK.hf g X = u + BK.hf f bk.E * c := by rw [← hc, hu]; ring
  show ‖ofPre l u ρ (am (BK.hf g X))‖ ≤ ρ
  rw [norm_ofPre, ← norm_preDisc, e2, map_add, map_mul]
  refine (um _ _).trans (max_le hX ?_)
  refine (norm_mul_le _ _).trans ?_
  calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul hE (norm_algebraMap_le _) (norm_nonneg _) hρ.le
    _ = ρ := mul_one _

theorem disc_map_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 →
    ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (BK.hf g) F := by
  intro l _ K bk B f g ρ h0 h1
  exact ⟨Disc.map (BK.hf g) (norm_toDisc_hf_le bk B f g ρ h0 h1), isDiscMap_map _ _⟩

end GlobalTheory.BSP.DiscPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_odAction : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  intro l _ Pl AI Td LL T
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdRp l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (cD Td b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (cD Td b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add, add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdRp l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdRp l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, cD_algebraMap, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl

end GlobalTheory.BKGal.JumpDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongrPowE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WApprox

theorem ρ₀_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by simp only [neg_neg_iff_pos]; positivity)

theorem exists_congr_pow_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ) (x : bk.DS bk.ρ₀),
    ∃ (k : ℕ) (s : bk.S), toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣
      (l : bk.DS bk.ρ₀) ^ k * x - toDisc l (X : bk.S) bk.ρ₀ s := by
  intro l _ K bk m
  induction m with
  | zero => intro x; exact ⟨0, 0, by simp⟩
  | succ m ih =>
    intro x
    obtain ⟨q, k, r, -, hx⟩ := WDiv.weierstrass_div l K bk bk.ρ₀ le_rfl (ρ₀_lt_one bk) x
    obtain ⟨k', s', w, hw⟩ := ih q
    refine ⟨k + k', bk.E * s' + (l : bk.S) ^ k' * (r : bk.S), w, ?_⟩
    have hq : (l : bk.DS bk.ρ₀) ^ k' * q = toDisc l (X : bk.S) bk.ρ₀ s' +
        toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m * w := by rw [← hw]; ring
    calc (l : bk.DS bk.ρ₀) ^ (k + k') * x - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S))
        = (l : bk.DS bk.ρ₀) ^ k' * ((l : bk.DS bk.ρ₀) ^ k * x) - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S)) := by ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E * ((l : bk.DS bk.ρ₀) ^ k' * q) - toDisc l (X : bk.S) bk.ρ₀ bk.E * toDisc l (X : bk.S) bk.ρ₀ s' := by
          rw [hx, map_add, map_mul, map_mul, map_pow, map_natCast]; ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (m + 1) * w := by rw [hq]; ring

end GlobalTheory.BKLim.WApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmuller
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CoverGen

open GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

theorem covers_of_sigma_teich {k : GQ l} (s : ZMod a) (z : Fq l a) (hze : z ^ e = 1)
    (hs : ∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w))
    (hz : ϖ.kummer k = Fq.val l a z) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd s⟩, fun f f' hf' => ?_⟩
  set m : ℕ := s.val with hmdef
  have hms : ((m : ℕ) : ZMod a) = s := ZMod.natCast_zmod_val s
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd s⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply, hms]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]
  rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hs, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz.symm, idem_mul_glue]

end GlobalTheory.CoverGen

theorem GlobalTheory.CoverGen.exists_covers_of_sigma_teich : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ s z hze hs hz => GlobalTheory.CoverGen.covers_of_sigma_teich t ϖ K s z hze hs hz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  first | exact @GlobalTheory.CrysExt.exists_coord | exact GlobalTheory.CrysExt.exists_coord | (intros; apply GlobalTheory.CrysExt.exists_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CDelta

variable {l : ℕ} [hl : Fact l.Prime] {L Q : Type} [CommRing L] [CommRing Q] {i : L →+* Q} {J : Ideal L}

omit hl in

theorem smul_top_eq (n : ℕ) : ((J.map i) ^ n • ⊤ : Submodule Q Q) = (J ^ n).map i := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]

omit hl in

theorem eq_of_forall (hc : IsCompl i J) {u v : Q} (h : ∀ n, u - v ∈ (J ^ n).map i) : u = v := by
  refine sub_eq_zero.1 (hc.complete.toIsHausdorff.haus (u - v) fun n => ?_)
  rw [SModEq.sub_mem, sub_zero, smul_top_eq]; exact h n

omit hl in
theorem mem_succ {x : Q} {n : ℕ} (h : x ∈ (J ^ (n + 1)).map i) : x ∈ (J ^ n).map i :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) h

theorem key (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) {x : Q} {a b : L} {n : ℕ}
    (ha : x - i a ∈ (J ^ (n + 1)).map i) (hb : x - i b ∈ (J ^ (n + 1)).map i) :
    i (D.δ a) - i (D.δ b) ∈ (J ^ n).map i := by
  have hab : a - b ∈ J ^ (n + 1) := hc.ker _ _ (by
    have := sub_mem hb ha
    rw [map_sub]; convert this using 1; ring)
  have h := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l L D J hlJ n b (a - b) hab
  rw [add_sub_cancel] at h
  rw [← map_sub]; exact Ideal.mem_map_of_mem _ h

theorem exists_lim (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) (x : Q) :
    ∃ z : Q, ∀ (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i → z - i (D.δ a) ∈ (J ^ n).map i := by
  choose ap hap using hc.surj x
  obtain ⟨z, hz⟩ := hc.complete.toIsPrecomplete.prec (f := fun n => i (D.δ (ap (n + 1)))) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_top_eq]
    exact key hc hlJ D (hap (m + 1)) (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hap (n + 1)))
  refine ⟨z, fun n a ha => ?_⟩
  have h1 := hz n
  rw [SModEq.sub_mem, smul_top_eq] at h1
  have h2 := key hc hlJ D (hap (n + 1)) ha
  have := sub_mem h2 h1
  convert this using 1; ring

end GlobalTheory.BSP.CDelta

open GlobalTheory.BSP.CDelta in

theorem GlobalTheory.BSP.exists_delta_completion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  intro l _ L _ Q _ i J hc hlJ D
  choose d hd using exists_lim hc hlJ D
  have sep : ∀ u v : W2 l Q, (∀ n, W2.map (Ideal.Quotient.mk ((J ^ n).map i)) u =
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) v) → u = v := by
    intro u v h
    have h1 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.fst = Ideal.Quotient.mk ((J ^ n).map i) v.fst :=
      fun n => congrArg W2.fst (h n)
    have h2 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.snd = Ideal.Quotient.mk ((J ^ n).map i) v.snd :=
      fun n => congrArg W2.snd (h n)
    exact W2.ext (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h1 n))
      (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h2 n))
  have ap : ∀ (x : Q) (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i →
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) (⟨x, d x⟩ : W2 l Q) =
        W2.map ((Ideal.Quotient.mk ((J ^ n).map i)).comp i) (deltaSectionToWittLengthTwo D a) := by
    intro x n a ha
    have h1 : Ideal.Quotient.mk ((J ^ n).map i) x = Ideal.Quotient.mk ((J ^ n).map i) (i a) :=
      Ideal.Quotient.eq.2 (mem_succ ha)
    have h2 : Ideal.Quotient.mk ((J ^ n).map i) (d x) = Ideal.Quotient.mk ((J ^ n).map i) (i (D.δ a)) :=
      Ideal.Quotient.eq.2 (hd x n a ha)
    exact W2.ext h1 h2
  let s : Q →+* W2 l Q :=
    { toFun := fun x => ⟨x, d x⟩
      map_one' := sep _ _ fun n => by
        rw [ap 1 n 1 (by simp), map_one, map_one, map_one]
      map_zero' := sep _ _ fun n => by
        rw [ap 0 n 0 (by simp), map_zero, map_zero, map_zero]
      map_add' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x + y - i (a + b) ∈ (J ^ (n + 1)).map i := by
          rw [map_add]; convert add_mem ha hb using 1; ring
        show W2.map _ (⟨x + y, d (x + y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) + ⟨y, d y⟩)
        rw [ap _ n _ hab, map_add (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_add (deltaSectionToWittLengthTwo D),
          map_add]
      map_mul' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x * y - i (a * b) ∈ (J ^ (n + 1)).map i := by
          have : x * y - i (a * b) = y * (x - i a) + i a * (y - i b) := by rw [map_mul]; ring
          rw [this]; exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
        show W2.map _ (⟨x * y, d (x * y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) * ⟨y, d y⟩)
        rw [ap _ n _ hab, map_mul (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_mul (deltaSectionToWittLengthTwo D),
          map_mul] }
  refine ⟨deltaStructureOfWittLengthTwoSection s fun _ => rfl, fun a => ?_⟩
  show i (D.δ a) = d (i a)
  exact (eq_of_forall hc fun n => hd (i a) n a (by simp)).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualSelmerClassNotKilledStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_selmer_class_not_killed : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))), Perf A β → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (c t : A) (y₀ : Fin a → A) (j : Fin a), (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ A g m = m) → t • m = 0) → Matrix.vecMul y₀ Φ = 0 → c * t * y₀ j ≠ 0 → ∃ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y ∧ ¬ Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) := by
  first | exact @GlobalTheory.NewPrime.DualClass.exists_not_cob | exact GlobalTheory.NewPrime.DualClass.exists_not_cob | (intros; apply GlobalTheory.NewPrime.DualClass.exists_not_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def boundedCoeffSeries (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] : Subalgebra O K⟦X⟧ where
  carrier := {f | ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c}
  mul_mem' hf hg := Hom.bdd_mul hf hg
  add_mem' hf hg := Hom.bdd_add hf hg
  algebraMap_mem' c := ⟨1, (A O K).algebraMap_mem c⟩

theorem Hom.exists_E_pow_mul_frob_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have key : ∀ {μ : Type} [Fintype μ] (Y : ZMod a → Matrix μ μ K⟦X⟧),
      (∀ τ i j, Y τ i j ∈ invE l e (A O K)) → ∃ n : ℕ, ∀ τ i j, E K l e ^ n * Y τ i j ∈ A O K := by
    intro μ _ Y hY
    choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
    refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (hn (τ, i, j))
  obtain ⟨n₁, hn₁⟩ := key P.mx P.mx_mem
  obtain ⟨n₂, hn₂⟩ := key Q.mxInv Q.mxInv_mem
  refine ⟨n₁ + n₂, fun τ h hh => ?_⟩
  obtain ⟨hb, Y, ⟨c, hc⟩, hF⟩ := hh
  have hA : ∀ f ∈ A O K, f ∈ boundedCoeffSeries O K := fun f hf => ⟨1, hf⟩
  have hfr : ∀ f ∈ boundedCoeffSeries O K, frob K l f ∈ boundedCoeffSeries O K := by
    rintro f ⟨d, hd⟩
    refine ⟨d, fun n => ?_⟩
    rw [coeff_frob]
    split_ifs
    · exact hd _
    · simpa using (norm_nonneg _).trans (hd 0)
  have hE : E K l e ∈ A O K := E_mem l e _
  refine ⟨mul_mem (hA _ (pow_mem hE _)) (hfr _ hb),
    (E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ), ?_, ?_⟩
  · have hmem : ∀ i j, ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ)) i j ∈
        boundedCoeffSeries O K := by
      intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact sum_mem fun k _ => mul_mem (sum_mem fun m _ =>
        mul_mem (hA _ (hn₁ τ i m)) (hfr _ ⟨c, fun n => hc m k n⟩)) (hA _ (hn₂ τ k j))
    choose d hd using hmem
    obtain ⟨D, hD⟩ := Finite.exists_le (fun p : ι × κ => d p.1 p.2)
    exact ⟨D, fun i j n => (hd i j n).trans (hD (i, j))⟩
  · have hmap : (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) =
        frob K l h • (1 : Matrix κ κ K⟦X⟧) := by
      have h1 : (F.mat (τ - 1) * Y).map (frob K l) = (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) :=
        Matrix.map_mul (f := (frob K l).toRingHom)
      rw [← h1, hF]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    calc F.mat τ * ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ))
        = (E K l e ^ n₁ * E K l e ^ n₂) • ((F.mat τ * P.mx τ) * Y.map (frob K l) * Q.mxInv τ) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = (E K l e ^ n₁ * E K l e ^ n₂) •
          (Q.mx τ * ((F.mat (τ - 1)).map (frob K l) * Y.map (frob K l)) * Q.mxInv τ) := by
          rw [F.comm, Matrix.mul_assoc (Q.mx τ)]
      _ = (E K l e ^ (n₁ + n₂) * frob K l h) • (1 : Matrix κ κ K⟦X⟧) := by
          rw [hmap, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mx_mul_mxInv, smul_smul, pow_add]

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixFlatOfTiltMapsAgreeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixFlat_of_tilt_maps_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ ψ' : OCb l →+* O, (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) → ∃ g : ↥(GK K), bk.FixFlat g ∧ ∀ y, ψ' y = ψ (Per.σF (g : GQ l) y) := by
  first | exact @GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree | exact GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree | (intros; apply GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobInvMulMemInerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frob_inv_mul_mem_inertia : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Fr : Gl l), (pc Pl h hN hF hS).IsFrob Fr → ∃ Φ : Gl l, (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Φ : GQ l) x - x ^ l‖ < 1) ∧ Φ⁻¹ * Fr ∈ (pc Pl h hN hF hS).Iner := by
  first | exact @GlobalTheory.FrobLiftUnr.exists_frob_inv_mul_mem_iner | exact GlobalTheory.FrobLiftUnr.exists_frob_inv_mul_mem_iner | (intros; apply GlobalTheory.FrobLiftUnr.exists_frob_inv_mul_mem_iner <;> assumption)
end

