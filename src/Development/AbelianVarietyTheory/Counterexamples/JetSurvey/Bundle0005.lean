import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0031
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsNabNotIsNablaPin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0021
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0029
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ChartIndepTruncOfExpGauge
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartIndepExpTest

open NumberField MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem psiCover {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : PsiCoverSt H := by
  intro τ
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]; simpa using this
  have hre : H.rt0.re = 0 := by
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im] at h2 h3
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at h2
    nlinarith [mul_self_nonneg H.rt0.re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact Or.inl h
  · right
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h]
    apply Complex.ext <;> simp [hre]

section Quad

variable {S : Type} [CommRing S] {d : ℕ}

abbrev sq2 (i j : Fin d) : Fin 1 × Fin d →₀ ℕ := Finsupp.single (0, i) 1 + Finsupp.single (0, j) 1

theorem exists_sq_of_degree_two (m : Fin 1 × Fin d →₀ ℕ) (hm : m.degree = 2) : ∃ i j, i ≤ j ∧ m = sq2 i j := by
  classical
  have hc : Multiset.card (Finsupp.toMultiset m) = 2 := by
    rw [Finsupp.card_toMultiset, ← hm]; rfl
  obtain ⟨⟨o, a⟩, ⟨o', b⟩, hab⟩ := Multiset.card_eq_two.1 hc
  obtain rfl : o = 0 := Subsingleton.elim _ _
  obtain rfl : o' = 0 := Subsingleton.elim _ _
  have : m = sq2 a b := by
    rw [← Finsupp.toMultiset_toFinsupp m, hab]
    ext x
    simp [Multiset.count_cons, Multiset.count_singleton, Finsupp.single_apply, eq_comm, add_comm]
  rcases le_total a b with h | h
  · exact ⟨a, b, h, this⟩
  · exact ⟨b, a, h, this.trans (add_comm _ _)⟩

theorem sq_monomial_injective {i j a b : Fin d} (hij : i ≤ j) (hab : a ≤ b) (h : sq2 i j = sq2 a b) : i = a ∧ j = b := by
  rcases (Finsupp.single_add_single_eq_single_add_single one_ne_zero one_ne_zero).1 h with
    ⟨h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨congrArg Prod.snd h1, congrArg Prod.snd h2⟩
  · have e1 : i = b := congrArg Prod.snd h1
    have e2 : j = a := congrArg Prod.snd h2
    subst e1 e2
    exact ⟨le_antisymm hij hab, le_antisymm hab hij⟩
  · omega

def quadMat (q : MvPowerSeries (Fin 1 × Fin d) S) : Matrix (Fin d) (Fin d) S :=
  fun i j => if i ≤ j then coeff (sq2 i j) q else 0

theorem eq_sum_quadMat (q : MvPowerSeries (Fin 1 × Fin d) S) (hq : ∀ m, coeff m q ≠ 0 → m.degree = 2) :
    q = ∑ p : Fin d × Fin d, C (quadMat q p.1 p.2) * X (0, p.1) * X (0, p.2) := by
  classical
  ext m
  have hc : ∀ p : Fin d × Fin d, coeff m (C (quadMat q p.1 p.2) * X ((0 : Fin 1), p.1) * X (0, p.2) :
      MvPowerSeries (Fin 1 × Fin d) S) = if m = sq2 p.1 p.2 then quadMat q p.1 p.2 else 0 := by
    intro p
    rw [mul_assoc, coeff_C_mul, X, X, monomial_mul_monomial, coeff_monomial]
    split_ifs <;> simp
  rw [map_sum]
  simp only [hc]
  by_cases hm : m.degree = 2
  · obtain ⟨a, b, hab, rfl⟩ := exists_sq_of_degree_two m hm
    rw [Finset.sum_eq_single (a, b)]
    · simp [quadMat, hab]
    · rintro ⟨i, j⟩ - hne
      split_ifs with h
      · by_cases hij : i ≤ j
        · obtain ⟨rfl, rfl⟩ := sq_monomial_injective hab hij h
          exact absurd rfl hne
        · simp [quadMat, hij]
      · rfl
    · simp
  · have h0 : coeff m q = 0 := by_contra fun h => hm (hq m h)
    rw [h0]
    refine (Finset.sum_eq_zero fun p _ => if_neg fun h => hm ?_).symm
    rw [h]; simp

end Quad

theorem killAddVal : KillAddValSt := by
  intro E _ _ _ H Dw l c S _ _ _ k n g q hq0 hq2 hqp a P hP
  have hβ : ∀ i j, quadMat q i j ≠ 0 →
      ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1 := by
    intro i j h
    refine hqp _ _ ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    intro h0
    apply h
    unfold quadMat
    split_ifs
    · exact h0
    · rfl
  let r : Fin n → Fin 1 × Fin (dL Dw) → Fin n × Fin (dL Dw) := fun b p => (b, p.2)
  have hK := killAddValCol_of (TB.killAdd_of TB.quadratic_column_derivative) E H Dw l c S k n
    (∏ b, rename (r b) (g b)) (quadMat q) (psiCover H) hβ a P hP
  have hcq : constantCoeff (-((k : S) • q)) = 0 := by simp [hq0]
  have hexp : ∀ b, rename (r b) (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) =
      Germ.FB.expS S (rename (r b) (-((k : S) • q))) := by
    intro b
    rw [rename_eq_subst, rename_eq_subst]
    simp only [Germ.FB.expS, PowerSeries.subst_def]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hcq)
      (hasSubst_of_constantCoeff_zero fun _ => by simp)]
  have hsum : ∑ b, rename (r b) (-((k : S) • q)) = -((k : S)) • TB.quadCol (n := n) (quadMat q) := by
    rw [TB.quadCol, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_neg, map_smul, neg_smul]
    congr 2
    conv_lhs => rw [eq_sum_quadMat q hq2]
    rw [map_sum, Fintype.sum_prod_type]
    simp only [map_mul, rename_C, rename_X, r]
  have hprod : ∏ b, rename (r b) (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) =
      Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) (quadMat q)) * ∏ b, rename (r b) (g b) := by
    rw [← hsum, GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion.expS_sum _ _ (fun b => by rw [constantCoeff_rename]; exact hcq),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => by rw [map_mul, hexp, mul_comm]
  rw [← hprod] at hK
  simpa only [r, prodCol_holds E H Dw S n] using hK

theorem expUniqTan : ExpUniqTanSt := ExpUniqChart.expUniqTan

theorem frTruncOfGerms : FrTruncOfGermsSt :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C h => GlobalTheory.NablaPinCompare.compat_of_germs C h

theorem chartIndepTrunc_of_expGauge (hG : ExpGaugeOfSt) : ChartIndepTruncSt :=
  chartIndepTrunc_of (expChartOf_of (expActOf_of LinEig.linEig_holds)) hG tie_holds expUniqTan
    (gaugeUniq_of_global GlobalTheory.SemiRigid.globalFns) killAddVal

theorem four_claims : ExpUniqTanSt ∧ KillAddValSt ∧ FrTruncOfGermsSt ∧ (ExpGaugeOfSt → ChartIndepTruncSt) :=
  ⟨expUniqTan, killAddVal, frTruncOfGerms, chartIndepTrunc_of_expGauge⟩

end GlobalTheory.ChartIndepExpTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.EqZeroOfPnorm
section
noncomputable section

namespace GlobalTheory.NetNormExamples

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg X la x)

theorem pnorm_le_supN (U : Unf Xo c σ r) (la) {P : FDSec U.X} (hP : P ∈ holSub U.X la) (p : FPt U.X) :
    (U.X p.1).pnorm (la p.1) (P p.1) p.2 ≤ supN U.X la P := by
  unfold supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem eq_zero_of_pnorm (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h0 : X.pnorm la P x = 0) : P x = 0 := by
  have hne : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i e => by
    have := (hx τ).2 i
    rw [e] at this; simp at this
  unfold Data.pnorm at h0
  refine norm_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (ne_of_gt ?_))
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hne _ _) (hne _ _))) _

theorem good_conj_iff (c : Coeff l) (σ : c.F →+* ℂ) : GoodEmb c (ComplexEmbedding.conjugate σ) ↔ ¬ GoodEmb c σ := by
  constructor
  · intro h1 h2
    have e : (starRingEnd ℂ) H.rt0 = H.rt0 := by
      have h3 : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h1
      rwa [show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h2] at h3
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp e
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  · intro h
    have := goodEmb_goodOf c σ
    unfold goodOf at this
    rwa [if_neg h] at this

theorem goodOf_conj (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c (ComplexEmbedding.conjugate σ) = goodOf c σ := by
  unfold goodOf
  by_cases h : GoodEmb c σ
  · rw [if_neg (fun h' => (good_conj_iff c σ).1 h' h), if_pos h]
    ext x; simp [ComplexEmbedding.conjugate]
  · rw [if_pos ((good_conj_iff c σ).2 h), if_neg h]; rfl

def coordAt (U : Unf Xo c σ r) (a : ℝ) (p : FPt U.X) : Rul Xo c →ₛₗ[σ] ℂ where
  toFun f := (a : ℂ) * rdU U f p.1 p.2
  map_add' f g := by rw [map_add, Pi.add_apply, Pi.add_apply, mul_add]
  map_smul' x f := by rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

end GlobalTheory.NetNormExamples
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePullExpands
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullEveryLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_pull_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (k N : ℕ) (s : U.SecK k) (s' : U.SecK (k * N))
    (h : IsPullByEnd U f k N s s') :
    ∃ c : ∀ y : (pullback G.hom (jK V) : Scheme.{0}), ((pullback G.hom (jK V) ⟶ G.left) → U.LG.L.ι) →
        (pullback G.hom (jK V) : Scheme.{0}).presheaf.stalk y,
      (∀ y J, Good U.LG.L y J → sval s' (𝟙 _) y J = sval s (endK f) y J * c y J) ∧
      ∀ (m : ℕ) (t : U.SecK (m * k)), ∃ t' : U.SecK (m * k * N), IsPullByEnd U f (m * k) N t t' ∧
        ∀ y J, Good U.LG.L y J → sval t' (𝟙 _) y J = sval t (endK f) y J * c y J ^ m := by
  obtain ⟨u, hu, hc, hr⟩ := h
  have hL := U.LG.isLB
  refine ⟨fun y J => (val u (𝟙 _) y J).val, fun y J hJ => ?_, fun m t => ?_⟩
  · have := (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 hr _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · obtain ⟨v, hv, hvv⟩ := exists_gen hL (φ' := ![gK, endK f ≫ gK])
      (ε' := ![((m * k * N : ℕ) : ℤ), -((m * k : ℕ) : ℤ)])
      (fun W _ h => by
        simp [Fin.prod_univ_two, _root_.mul_assoc])
      (GeneratorPullback.powGen U.LG.L _ _ u m) (powGen_isGen_of_isGen u hu m)
    obtain ⟨t', ht'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => gK) (ε' := fun _ => ((m * k * N : ℕ) : ℤ))
      (fun W _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
          Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
        rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec t (endK f) v hv)
    have key : ∀ y J, Good U.LG.L y J →
        sval t' (𝟙 _) y J = sval t (𝟙 _ ≫ endK f) y J * (val v (𝟙 _) y J).val := fun y J hJ => by
      rw [ht' _ _ y J hJ, sval_pullMulSec _ _ _ _ _ y hJ]
    refine ⟨t', ⟨v, hv, ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 key⟩, fun y J hJ => ?_⟩
    · refine corr_of_val hL fun z J hJ => ?_
      have e := val_corr hJ hc (𝟙 _)
      rw [val_pull hJ, val_pull hJ, val_pow] at e
      rw [val_pull hJ, val_pull hJ, val_pow, hvv _ _ z J hJ, val_pow, e, ← pow_mul]
      congr 1
      ring
    · rw [key y J hJ, Category.id_comp, hvv _ _ y J hJ, val_pow, Units.val_pow_eq_pow_val]

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Geo.Tor.Host E}
  {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}

theorem expands_pull_every_level (hLaws : Laws) (P : Geo.Tor.PELUnif (maximalIdeal V) t)
    (a : NumberField.RingOfIntegers E) (N : ℕ)
    (hN : letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) (hN0 : 0 < N) {k : ℕ} (hk : 1 ≤ k)
    (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (hs : P.U.Expands k s F)
    (s' : P.U.SecK (k * N)) (hs' : IsPullByEnd P.U (t.act.act a) k N s s') :
    letI := H.starRing
    ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧
      PullAl P.D (FractionRing V) P.oD a k N F F' := by
  letI := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  obtain ⟨F', hF'⟩ := exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
    (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  obtain ⟨s'', hs'', -⟩ := (P.U.expand (k * N) (Nat.mul_pos hk hN0)).2 F'
  obtain ⟨c, hc, hpow⟩ := exists_pull_pow P.U _ k N s s' hs'
  have hint := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ _ _ _
    P.U.toUnifPre).2
  have e : s'' = s' := by
    refine SecOps.sec_ext (sec_ext_val P.U.LG.isLB fun y J hJ => ?_)
    have hm : ∀ m : ℕ, 4 ≤ m → sval s'' (𝟙 _) y J ^ m = sval s' (𝟙 _) y J ^ m := fun m hm => by
      have hmk : 4 ≤ m * k := le_trans hm (Nat.le_mul_of_pos_right m hk)
      obtain ⟨τ, hτ⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ _ _ _ P.U.toUnifPre (m * k) hmk _
        (endK (t.act.act a)) y J hJ
      obtain ⟨τ', hτ', hv⟩ := hpow m τ
      obtain ⟨T, hT, -⟩ := (P.U.expand (m * k) (by omega)).1 τ
      obtain ⟨T', hT', hTT⟩ := GlobalTheory.PullExpansion.expands_pull_of_four_le hLaws V E H t P a N hN hN0 (m * k) hmk
        τ T hT τ' hτ'
      have g := GlobalTheory.GenericCross.main hLaws V E H t P a N hN hN0 k s F s'' F' hs hs'' hF' (m * k) τ T τ' T' hT hT'
        hTT m 1 (by ring) y J hJ
      rw [pow_one, pow_one, hv y J hJ] at g
      refine hτ.mul_right_cancel (g.trans ?_)
      rw [hc y J hJ]
      ring
    exact GlobalTheory.PullLevelOne.eq_of_pow_four_five (hm 4 le_rfl) (hm 5 (by norm_num))
  exact ⟨F', e ▸ hs'', hF'⟩

end

end GlobalTheory.PullEveryLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FramePointsTrunc
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpPiecesCheck

theorem linEig : LinEigSt := LinEig.linEig_holds

theorem expChartOf : ExpChartOfSt := expChartOf_of (expActOf_of linEig)

theorem commonCoc : CommonCocSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x _ e e' he he' a
  obtain ⟨β, hg, hr, hc⟩ := he.coc a
  obtain ⟨β', hg', hr', hc'⟩ := he'.coc a
  obtain rfl := betaUniq_of_global GlobalTheory.SemiRigid.globalFns E H Dw l Xo a β β' hg hg' hr hr'
  exact ⟨β, hg, hr, hc, hc'⟩

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

end

theorem three_hold : ExpChartOfSt ∧ LinEigSt ∧ CommonCocSt := ⟨expChartOf, linEig, commonCoc⟩

end GlobalTheory.ExpPiecesCheck
end
end

