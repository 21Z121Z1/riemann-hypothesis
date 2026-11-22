import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyLeviShift
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section

namespace GlobalTheory.LeviShift

theorem sum_H0_parabolic_mul : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ (j : Fin (wittIndex V)) (q y : GA D V),
      q ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) →
      ∑ i ∈ Finset.Iic j, H0 Φ (levelAll D.sp.cm.sig V.gram L a) (q * y) i =
        logDelta Φ (stdVec j) q + ∑ i ∈ Finset.Iic j, H0 Φ (levelAll D.sp.cm.sig V.gram L a) y i := by
  intro D V Φ L a hg j q y hq
  have hK := hg.isCompact
  have hP0 : ∀ p : PA Φ.flag0, (p : GA D V) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) :=
    fun p => by rw [Φ.sub_stdVec]; exact Φ.flag0.par_le_parab _ _ j.succ p.2
  obtain ⟨p, k, hk, rfl⟩ := GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg y
  obtain ⟨p', k', hk', e⟩ := GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg (q * p)
  have hqy : q * (p * k) = p' * (k' * k) := by rw [← mul_assoc, e, mul_assoc]
  have hk'P : k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) := by
    have : k' = (p' : GA D V)⁻¹ * (q * p) := by rw [e]; group
    rw [this]; exact mul_mem (inv_mem (hP0 p')) (mul_mem hq (hP0 p))
  have hpos : ∀ (r : PA Φ.flag0) (i : Fin (wittIndex V)), ((absChi Φ i r : NNReal) : ℝ) ≠ 0 := fun r i =>
    NNReal.coe_ne_zero.2 (GlobalTheory.Doubling.hom_pos _ r).ne'
  simp only [hqy, mul_mem_riemannRochSpace_add hK _ (mul_mem hk' hk), mul_mem_riemannRochSpace_add hK _ hk]
  rw [← Real.log_prod (fun i _ => hpos p' i), ← Real.log_prod (fun i _ => hpos p i), ← NNReal.coe_prod,
    ← NNReal.coe_prod, GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p', GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p]
  have m1 := GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) q p hq (hP0 p)
  have m2 := GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) p' k' (hP0 p') hk'P
  have h3 := GlobalTheory.T.level_parabolic_determinant_abs_one D V Φ L a hg (stdVec j) k' hk' hk'P
  rw [← e] at m2
  have key : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') =
      absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) q) *
        absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
    have := congrArg (absA D.host.F D.host.E) (m1.symm.trans m2)
    rw [absA_mul, absA_mul, h3, mul_one] at this; exact this.symm
  have n1 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') ≠ 0 := by
    rw [← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]; exact (Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'
  have n2 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) ≠ 0 := by
    rw [← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]; exact (Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'
  rw [key] at n1 ⊢
  unfold logDelta
  rw [NNReal.coe_mul, Real.log_mul (NNReal.coe_ne_zero.2 (left_ne_zero_of_mul n1)) (NNReal.coe_ne_zero.2 n2)]

theorem inner_vector_inverse_levi_shift {k : ℕ} (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (j : Fin k) (H : A0 k) :
    inner ℝ (vec (invSV π ε (stdVec j))) (inverseChamberMap π ε H) = ∑ i ∈ Finset.Iic j, H i := by
  have sq : ∀ e : SignTypeˣ, ((e : SignType) : ℝ) * (e : SignType) = 1 := fun e => by
    by_cases h : e = 1
    · simp [h]
    · rw [sign_unit e h]; norm_num
  simp only [PiLp.inner_apply, vec, invSV, inverseChamberMap, RCLike.inner_apply, conj_trivial]
  have e : ∀ x, ((ε x : SignType) : ℝ) * H.ofLp (π x) * (((ε x : SignType) * stdVec j (π x) : SignType) : ℝ) =
      H.ofLp (π x) * (stdVec j (π x) : ℝ) := fun x => by
    rw [SignType.coe_mul]; linear_combination (H.ofLp (π x) * (stdVec j (π x) : ℝ)) * sq (ε x)
  simp only [e]
  rw [Equiv.sum_comp π (fun i => H.ofLp i * (stdVec j i : ℝ)),
    show Finset.Iic j = Finset.univ.filter (· ≤ j) by ext; simp, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ j <;> simp [stdVec, h]

theorem yfam_mul_levi : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ Q ∈ parP (aP P) ∅, ∀ x Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (m * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q + pr Q h := by
  intro D V Φ L a hg P hP m hm
  obtain ⟨h, hh⟩ := GlobalTheory.T.levi_log_modulus_vector D V Φ P hP m hm
  refine ⟨h, fun Q hQ x T => ?_⟩
  obtain ⟨hQp, hQa, -⟩ := mem_parP.1 hQ
  obtain ⟨π, ε, w, hw, hsub, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQp
  rw [hY, hY, ← sub_eq_iff_eq_add', ← map_sub, ← sub_eq_zero, ← map_sub, pr, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.mem_orthogonal]
  intro v hv
  refine Submodule.span_induction (p := fun v _ => inner ℝ v _ = (0:ℝ)) ?_ (by simp)
    (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero])
    (fun c x _ hx => by rw [inner_smul_left, hx, mul_zero]) hv
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 (hsub hu)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hs
  have hvu : vec (invSV π ε (stdVec j)) ∈ aP P := hQa ▸ Submodule.subset_span ⟨_, hu, rfl⟩
  have hmu : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) := by
    have := GlobalTheory.T.levi_monotone_in_parabolic D V Φ (AF D.host.F) P hP _ hvu hm
    have h2 : Φ.levi D.sp.cm (AF D.host.F) {invSV π ε (stdVec j)} ≤
        GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) := by
      unfold WittFrame.levi
      exact (iInf₂_le (invSV π ε (stdVec j)) (Finset.mem_singleton_self _)).trans inf_le_left
    exact h2 this
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.weyl_conjugate_parabolic_log_modulus D V Φ π ε w hw j m hmu
  have e1 := sum_H0_parabolic_mul D V Φ L a hg j _ (rat V w * x) hg1
  have e2 : rat V w * (m * x) = rat V w * m * (rat V w)⁻¹ * (rat V w * x) := by group
  simp only [Ys, inner_sub_right, inner_vector_inverse_levi_shift, hh _ hvu, e2, PiLp.sub_apply, Finset.sum_sub_distrib] at e1 ⊢
  rw [e1, hg2]
  ring

end GlobalTheory.LeviShift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyPlaceAdditive
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped NNReal

namespace GlobalTheory.TruncKer.PlaceAdd

section Abstract

variable {G : Type} [Group G] {P : Subgroup G} {δ : P →* ℝ≥0} {K : Subgroup G} (h : Doubling.IsIwasawa δ K)
  (e : G →* G) (hP : ∀ p ∈ P, e p ∈ P) (hK : ∀ k ∈ K, e k ∈ K) (hc : ∀ a b, Commute (e a) ((e b)⁻¹ * b))
include h hP hK hc

theorem iwAbs_eq_mul (g : G) :
    Doubling.iwAbs δ K g = Doubling.iwAbs δ K (e g) * Doubling.iwAbs δ K ((e g)⁻¹ * g) := by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  let q : P := ⟨e p, hP _ p.2⟩
  have e1 : e (p * k) = (q : G) * e k := map_mul _ _ _
  have e2 : (e (p * k))⁻¹ * (p * k) = ((q⁻¹ * p : P) : G) * ((e k)⁻¹ * k) := by
    have := (hc k p).inv_left.eq
    change _ = (e p)⁻¹ * p * ((e k)⁻¹ * k)
    rw [← mul_assoc _ (e k)⁻¹, ← this, map_mul]
    group
  rw [e2, e1, h.iwAbs_mul _ hk, h.iwAbs_mul _ (hK _ hk), h.iwAbs_mul _ (mul_mem (inv_mem (hK _ hk)) hk), ← map_mul,
    mul_inv_cancel_left]

theorem iwAbs_four (w : G) {y z : G} (hy : e y = y) (hz : e z = 1) :
    Doubling.iwAbs δ K (w * (y * z)) * Doubling.iwAbs δ K w =
      Doubling.iwAbs δ K (w * y) * Doubling.iwAbs δ K (w * z) := by
  have c : y⁻¹ * ((e w)⁻¹ * w) = (e w)⁻¹ * w * y⁻¹ := by
    have := (hc y w).inv_left.eq
    rwa [hy] at this
  have a1 : e (w * (y * z)) = e (w * y) := by simp [hz]
  have a2 : e (w * z) = e w := by simp [hz]
  have b2 : (e (w * y))⁻¹ * (w * y) = (e w)⁻¹ * w := by
    rw [map_mul, hy, mul_inv_rev, mul_assoc, ← mul_assoc (e w)⁻¹, ← mul_assoc, c, inv_mul_cancel_right]
  have b1 : (e (w * y))⁻¹ * (w * (y * z)) = (e w)⁻¹ * (w * z) := by
    rw [← mul_assoc w, ← mul_assoc, b2, mul_assoc]
  rw [iwAbs_eq_mul h e hP hK hc (w * (y * z)), iwAbs_eq_mul h e hP hK hc w, iwAbs_eq_mul h e hP hK hc (w * y),
    iwAbs_eq_mul h e hP hK hc (w * z), a1, a2, b1, b2]
  ring

end Abstract

variable {D : D7} {V : HSp D} {Φ : WittFrame V} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
  {a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)}

theorem isIwasawa (hg : Φ.IsGood D.sp.cm L a) (i : Fin (wittIndex V)) :
    Doubling.IsIwasawa (absChi Φ i) (levelAll D.sp.cm.sig V.gram L a) := by
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  exact Doubling.isIwasawa_of_isCompact (Φ.flag0.isClosed_par _ _) (continuous_absChi i) hg.isCompact
    (GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg)

theorem continuous_H0 (hg : Φ.IsGood D.sp.cm L a) : Continuous (H0 Φ (levelAll D.sp.cm.sig V.gram L a)) := by
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact (NNReal.continuous_coe.comp ((isIwasawa hg i).continuous_iwAbs (Φ.flag0.isClosed_par _ _)
    (continuous_absChi i) hg.isCompact)).log fun x => NNReal.coe_ne_zero.2 (Doubling.iwAbs_pos _ _ x).ne'

theorem H0_mul_mul_add_eq_add (hg : Φ.IsGood D.sp.cm L a) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : GA D V) {y z : GA D V}
    (hy : y ∈ atPts D.sp.cm.sig V.gram S) (hz : z ∈ awayPts D.sp.cm.sig V.gram S) (i : Fin (wittIndex V)) :
    H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * (y * z)) i + H0 Φ (levelAll D.sp.cm.sig V.gram L a) w i =
      H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * y) i + H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * z) i := by
  let e : GA D V →* GA D V := (embAt D.sp.cm.sig V.gram S).comp (projAt D.sp.cm.sig V.gram S)
  have hm : ∀ g, e g ∈ atPts D.sp.cm.sig V.gram S := fun g => embAt_mem _ _ S _
  have hA : ∀ g u, projArch D.sp.cm.sig V.gram u (e g) = 1 := fun g =>
    mem_finPts_iff_forall.1 (mem_atPts.1 (hm g)).1
  have hF : ∀ g v, proj D.sp.cm.sig V.gram v (e g) = proj D.sp.cm.sig V.gram v g ∨
      proj D.sp.cm.sig V.gram v (e g) = 1 := fun g v => by
    by_cases hv : v ∈ S
    · exact .inl (proj_embAt _ _ S _ ⟨v, hv⟩)
    · exact .inr ((mem_atPts.1 (hm g)).2 v hv)
  have key := iwAbs_four (isIwasawa hg i) e (fun p hp => IsoFlag.mem_par_adelic.2
      ⟨fun u => by rw [hA]; exact one_mem _, fun v => by
        rcases hF p v with h | h <;> rw [h]
        exacts [(IsoFlag.mem_par_adelic.1 hp).2 v, one_mem _]⟩)
    (fun k hk => mem_levelAll.2 ⟨fun v => by
        rcases hF k v with h | h <;> rw [h]
        exacts [(mem_levelAll.1 hk).1 v, one_mem _], fun u => by rw [hA]; exact one_mem _⟩)
    (fun b c => commute_atPts_awayPts _ _ (hm b) (partAway D.sp.cm.sig V.gram S c).2) w (y := y) (z := z)
    (by
      obtain ⟨x, rfl⟩ := (range_embAt D.sp.cm.sig V.gram S).ge hy
      exact congrArg (embAt D.sp.cm.sig V.gram S) (projAt_embAt _ _ S x))
    (by
      have : projAt D.sp.cm.sig V.gram S z = 1 := funext fun v => mem_awayPts.1 hz v v.2
      exact (congrArg (embAt D.sp.cm.sig V.gram S) this).trans (map_one _))
  have n : ∀ x, ((Doubling.iwAbs (absChi Φ i) (levelAll D.sp.cm.sig V.gram L a) x : ℝ≥0) : ℝ) ≠ 0 := fun x =>
    NNReal.coe_ne_zero.2 (Doubling.iwAbs_pos _ _ x).ne'
  change Real.log _ + Real.log _ = Real.log _ + Real.log _
  rw [← Real.log_mul (n _) (n _), ← Real.log_mul (n _) (n _), ← NNReal.coe_mul, ← NNReal.coe_mul, key]

end GlobalTheory.TruncKer.PlaceAdd

namespace GlobalTheory.TruncKer

open PlaceAdd in

theorem yfam_continuous_add : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → (∀ Tr, Continuous fun x => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q) ∧ ∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, ∀ Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr Q = (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 Q - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0 Q) + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q := by
  intro D V Φ L a hg Q hQ
  obtain ⟨π, ε, w, -, -, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQ
  refine ⟨fun Tr => ?_, fun S y hy z hz Tr => ?_⟩
  · simp only [hY]
    refine (pr Q).continuous.comp ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_))
    exact continuous_const.mul ((PiLp.continuous_apply 2 _ (π i)).comp
      (continuous_const.sub ((continuous_H0 hg).comp (continuous_const.mul continuous_id))))
  · rw [hY, hY, hY, hY, ← map_sub, ← map_add]
    congr 1
    ext i
    have := H0_mul_mul_add_eq_add hg S (rat V w) hy hz (π i)
    simp only [Ys, inverseChamberMap, PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply, mul_one]
    linear_combination (-((ε i : SignType) : ℝ)) * this

end GlobalTheory.TruncKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionRealPointFockVectorsScalarColumnAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.RealColAct

open GlobalTheory.Ker.ColChange

theorem pureTensor_compAt {D : D7} {S T : HSp D} (C : Ctx S T) (h : GA D S) {B : C.Bas} (hB : C.IsB B)
    {f : WO S T → ℂ} (hf : C.IsTh f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
      C.fvec B f (ColChange.sub C h Q) := by
  have hU : ∀ τ, (compAt C.θ τ (Formalism.L2.Theta.mt S h))⁻¹ = (compAt C.θ τ (Formalism.L2.Theta.mt S h))ᴴ := fun τ =>
    Matrix.inv_eq_left_inv (GlobalTheory.Ker.ColChange.compAt_unitary C h τ)
  have key : ∀ g : WO S T → ℂ, C.IsTh g → ∀ v : FVar D T.rank S.rank,
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B v g =
        ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
            else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) •
          aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B (v.1, v.2.1, l) g := by
    rintro g hg ⟨τ, i, j⟩
    have hc : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g =
        ((fockScale D τ : ℂ)⁻¹) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g := by
      intro z
      rw [GlobalTheory.Ker.FockAlg.aPlus_eq C]
      unfold crea
      rw [sub_eq_add_neg, neg_smul]
    change aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap (compAt C.θ τ (Formalism.L2.Theta.mt S h)) (B τ) i j) g =
      ∑ l, (if (i : ℕ) < C.X.p0 then conj (compAt C.θ τ (Formalism.L2.Theta.mt S h) l j)
            else compAt C.θ τ (Formalism.L2.Theta.mt S h) l j) •
        aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap 1 (B τ) i l) g
    simp only [hc]
    rw [GlobalTheory.Ker.ColChange.unitMap_expand, GlobalTheory.Ker.ColChange.crea_sum C hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [GlobalTheory.Ker.ColChange.crea_smul C hg τ (C.sB B τ) (unitMap 1 (B τ) i l) ((i : ℕ) < C.X.p0)
      (GlobalTheory.Ker.ColChange.sB_unitMap C hB τ i l), hU τ, Matrix.conjTranspose_apply, smul_smul, smul_smul]
    congr 1
    split_ifs <;> simp [Complex.star_def, mul_comm]
  have Lc := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf P
  have L1 := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf P
  have hX : ∀ v : FVar D T.rank S.rank, ColChange.sub C h (MvPolynomial.X v) =
      ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
          else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) • MvPolynomial.X (v.1, v.2.1, l) := fun v =>
    MvPolynomial.aeval_X _ v
  show pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B f (ColChange.sub C h Q)
  induction Q using MvPolynomial.induction_on
  next a =>
    have e : (MvPolynomial.C a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • 1 := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_one (ColChange.sub C h), (Lc 1).2.2.1, (L1 1).2.2.1]
  next p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq]
  next p v hp =>
    rw [mul_comm p, (Lc p).2.1 v, hp, key _ (L1 (ColChange.sub C h p)).1 v, map_mul, hX, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, map_smul, (L1 (ColChange.sub C h p)).2.1]

theorem om_real_fvec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ h ∈ GinfC S, ∃ c : ℂ, c ≠ 0 ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom (GlobalTheory.Ker.ColChange.colU C h) (C.toH Q) → om (h, 1) (C.fvec B f Q) = c • C.fvec B f Q' := by
  intro D S T C om hom B hB f hf hF h hh
  obtain ⟨φ, hφ, hfφ⟩ := GlobalTheory.Ker.exists_test_of_fock D S T C B hB f hf hF
  obtain ⟨c, hc, hcφ⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom h hh 1 (one_mem _) B hB
  have h1 : C.mvB 1 B = B := GlobalTheory.Ker.ONBasis.mvB_fin C B (one_mem _)
  have hom1 : om (h, 1) f = c • f := by rw [hfφ, hcφ φ hφ, h1]
  refine ⟨c, fun h0 => by simp [h0] at hc, fun Q Q' hQ => ?_⟩
  have hQ' : Q' = ColChange.sub C h Q := C.toH_bijective.1 (by
    rw [hQ]; exact (DFunLike.congr_fun (GlobalTheory.Ker.ColChange.toH_sub C h) Q).symm)
  rw [hQ', GlobalTheory.Ker.WeakMove.om_fvec C hom h 1 hf B Q, h1, hom1,
    pureTensor_compAt C h hB (GlobalTheory.Ker.FockAlg.th_smul C c hf) Q]
  exact (GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf (ColChange.sub C h Q)).2.2.2.2.1 c

end GlobalTheory.Ker.RealColAct

end
end

