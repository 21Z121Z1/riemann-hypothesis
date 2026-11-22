import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartEqOfThetaOperatorEqStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_eq_of_thetaOperator_eq : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b := by
  first | exact @GlobalTheory.PhiBase.b_eq_of_phiRel | exact GlobalTheory.PhiBase.b_eq_of_phiRel | (intros; apply GlobalTheory.PhiBase.b_eq_of_phiRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

section RationalValues

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem le_iff_of_pow_eq_zpow {t a b : Γ} (h0 : 0 < t) (h1 : t < 1) {n n' : ℕ} (hn : 0 < n)
    (hn' : 0 < n') {m m' : ℤ} (ha : a ^ n = t ^ m) (hb : b ^ n' = t ^ m') :
    b ≤ a ↔ (m : ℚ) / n ≤ (m' : ℚ) / n' := by
  have e1 : a ^ (n * n') = t ^ (m * n') := by rw [pow_mul, ha, zpow_mul, zpow_natCast]
  have e2 : b ^ (n * n') = t ^ (m' * n) := by rw [mul_comm n, pow_mul, hb, zpow_mul, zpow_natCast]
  rw [← pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_pos hn hn').ne', e1, e2,
    zpow_le_zpow_iff_right_of_lt_one₀ h0 h1, div_le_div_iff₀ (by exact_mod_cast hn)
      (by exact_mod_cast hn')]
  norm_cast

theorem exists_ratAddValuation_of_pow_eq_zpow {F : Type*} [Field F] (w : Valuation F Γ) {t : Γ}
    (h0 : 0 < t) (h1 : t < 1) (h : ∀ x : F, x ≠ 0 → ∃ (n : ℕ) (m : ℤ), 0 < n ∧ w x ^ n = t ^ m) :
    ∃ v : AddValuation F (WithTop ℚ), ∀ (x : F) (m : ℤ), w x = t ^ m →
      v x = ((m : ℚ) : WithTop ℚ) := by
  classical
  choose! n m hn hnm using h
  let f : F → WithTop ℚ := fun x => if x = 0 then ⊤ else (((m x : ℚ) / n x : ℚ) : WithTop ℚ)
  have f0 : f 0 = ⊤ := if_pos rfl
  have key : ∀ (x : F) (a : ℕ) (b : ℤ), 0 < a → w x ^ a = t ^ b →
      f x = (((b : ℚ) / a : ℚ) : WithTop ℚ) := by
    intro x a b ha hab
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow ha.ne'] at hab
      exact (zpow_pos h0 b).ne hab
    simp only [f, if_neg hx, WithTop.coe_inj]
    exact le_antisymm ((le_iff_of_pow_eq_zpow h0 h1 (hn x hx) ha (hnm x hx) hab).1 le_rfl)
      ((le_iff_of_pow_eq_zpow h0 h1 ha (hn x hx) hab (hnm x hx)).1 le_rfl)
  have mono : ∀ x y : F, w y ≤ w x → f x ≤ f y := by
    intro x y hxy
    by_cases hy : y = 0
    · rw [hy, f0]; exact le_top
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff, Valuation.zero_iff] at hxy
      exact hy hxy
    simp only [f, if_neg hx, if_neg hy, WithTop.coe_le_coe]
    exact (le_iff_of_pow_eq_zpow h0 h1 (hn x hx) (hn y hy) (hnm x hx) (hnm y hy)).1 hxy
  refine ⟨AddValuation.of f f0 ?_ ?_ ?_, fun x b hb => ?_⟩
  · rw [key 1 1 0 one_pos (by simp)]
    simp
  · intro x y
    rcases le_max_iff.1 (w.map_add x y) with h | h
    · exact min_le_of_left_le (mono _ _ h)
    · exact min_le_of_right_le (mono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, MulZeroClass.zero_mul, f0, top_add]
    by_cases hy : y = 0
    · rw [hy, MulZeroClass.mul_zero, f0, add_top]
    have hx' := hn x hx
    have hy' := hn y hy
    rw [key (x * y) (n x * n y) (m x * n y + m y * n x) (Nat.mul_pos hx' hy') (by
      rw [map_mul, mul_pow, pow_mul, mul_comm (n x), pow_mul, hnm x hx, hnm y hy,
        zpow_add₀ h0.ne', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast])]
    simp only [f, if_neg hx, if_neg hy, ← WithTop.coe_add, WithTop.coe_inj]
    have : (n x : ℚ) ≠ 0 := by exact_mod_cast hx'.ne'
    have : (n y : ℚ) ≠ 0 := by exact_mod_cast hy'.ne'
    push_cast
    field_simp
  · change f x = _
    rw [key x 1 b one_pos (by simpa using hb)]
    simp

theorem exists_valuation_pow_eq_of_isAlgebraic {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Valuation F Γ) {x : F} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
  classical
  obtain ⟨p, hp0, hp⟩ := hx
  let g : ℕ → F := fun i => algebraMap K F (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, g i = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp
    exact hp
  have hc : ∀ i ∈ p.support, w (algebraMap K F (p.coeff i)) ≠ 0 := fun i hi => by
    simpa using hi
  have hw : w x ≠ 0 := by simpa using hx0
  have aux : ∀ i ∈ p.support, ∀ j ∈ p.support, j < i → w (g i) = w (g j) →
      ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
    intro i hi j hj hji e
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hji
    refine ⟨d + 1, p.coeff j / p.coeff (j + d + 1), Nat.succ_pos d,
      div_ne_zero (Polynomial.mem_support_iff.1 hj) (Polynomial.mem_support_iff.1 hi), ?_⟩
    simp only [g, map_mul, map_pow] at e
    rw [map_div₀, map_div₀, eq_div_iff (hc _ hi)]
    apply mul_right_cancel₀ (pow_ne_zero j hw)
    rw [← e, _root_.add_assoc j, pow_add (w x) j]
    ac_rfl
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun i => w (g i))
    (Polynomial.support_nonempty.2 hp0)
  by_contra hne
  have hlt : ∀ j ∈ p.support \ {i}, w (g j) < w (g i) := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    refine lt_of_le_of_ne (hmax j hj.1) fun e => hne ?_
    rcases lt_or_gt_of_ne hj.2 with h | h
    · exact aux i hi j hj.1 h e.symm
    · exact aux j hj.1 i hi h e
  have hgi : w (g i) ≠ 0 := by
    simp only [g, map_mul, map_pow]
    exact mul_ne_zero (hc i hi) (pow_ne_zero i hw)
  have := w.map_sum_eq_of_lt hi hlt
  rw [hsum, map_zero] at this
  exact hgi this.symm

end RationalValues

theorem exists_valOver_of_isAlgebraic {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] :
    ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by
  let K := FractionRing V
  let f : V →+* F := (algebraMap K F).comp (algebraMap V K)
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective V K)
  obtain ⟨W, hW⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨hW1, hW2⟩ := (localSubring_range_le_valuationSubring_iff f W).1 hW
  let w := W.valuation
  have h0 : 0 < w (f ϖ) := by
    rw [Valuation.pos_iff]
    exact (map_ne_zero_iff _ hf).2 hϖ.ne_zero
  have h1 : w (f ϖ) < 1 := (W.mem_nonunits_iff).1 (hW2 ϖ hϖ.not_isUnit)
  have hu : ∀ u : Vˣ, w (f u) = 1 := fun u =>
    W.valuation_unit (Units.map (f.codRestrict W hW1 : V →* W) u)
  have hval : ∀ (c : K) (n : ℤ), HasVal ϖ c n → w (algebraMap K F c) = w (f ϖ) ^ n := by
    rintro c n ⟨u, rfl⟩
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀]
    change w (f ϖ) ^ n * w (f u) = _
    rw [hu, _root_.mul_one]
  obtain ⟨v, hv⟩ := exists_ratAddValuation_of_pow_eq_zpow w h0 h1 fun x hx => by
    obtain ⟨n, c, hn, hc, e⟩ := exists_valuation_pow_eq_of_isAlgebraic (K := K) w
      (Algebra.IsAlgebraic.isAlgebraic x) hx
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    exact ⟨n, m, hn, e.trans (hval c m hm)⟩
  exact ⟨v, fun c n hc => hv _ n (hval c n hc)⟩

theorem exists_complete_discreteValuationRing_map_le {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V := by
  by_cases h : I = ⊥
  · let K := FractionRing R
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance,
      (PowerSeries.C (R := K)).comp (algebraMap R K), ?_,
      PowerSeries.C_injective.comp (IsFractionRing.injective R K), by simp [h]⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  · obtain ⟨p, hp, hIp⟩ := I.exists_le_maximal hI
    have := hp.isPrime
    obtain ⟨O, _, _, _, hO, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt
      (⊥ : Ideal R) p (lt_of_lt_of_le (bot_lt_iff_ne_bot.2 h) hIp)
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ, hO,
      (RingHom.injective_iff_ker_eq_bot φ).2 h1, Ideal.map_le_iff_le_comap.2 (h2 ▸ hIp)⟩

theorem adic_base_embeds_valuation_algebraic_closure :
    (∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V), IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v := by
  refine ⟨fun R _ _ _ I hR => ?_, fun V _ _ _ ϖ hϖ => exists_valOver_of_isAlgebraic hϖ _⟩
  obtain ⟨hN, -, -, hc⟩ := hR
  refine exists_complete_discreteValuationRing_map_le ?_
  rintro rfl
  exact not_subsingleton R (IsHausdorff.subsingleton hc.toIsHausdorff)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPsiOnBasicOpen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcPsiOn

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull

theorem genRel_iff_val {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) (z : Sp F) :
    GenRel w t t₀ x ↔ pt PUnit.unit ≫ φ = pt₀ PUnit.unit ∧ ∀ J₀ J, Good M₀ z J₀ → Good M z J →
      (om w z J₀ J (pt PUnit.unit) ^ ε PUnit.unit * val t (𝟙 _) z J).val = toStk z x * (val t₀ (𝟙 _) z J₀).val := by
  rw [genRel_iff w t t₀ x z]
  constructor
  · rintro ⟨hp, H⟩
    refine ⟨hp _, fun J₀ J hJ₀ hJ => ?_⟩
    have e := H (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ)) (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
    rw [Fintype.prod_unique] at e
    rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ z J₀ (fun k => J₀ (pt k ≫ φ)) (fun k => by rw [Category.id_comp, hp])]
    exact e
  · rintro ⟨hp, H⟩
    refine ⟨fun _ => hp, fun j j₀ h₀ h₁ => ?_⟩
    obtain ⟨J, hJ, eJ⟩ := exists_good M hM z pt j (fun _ _ _ => rfl) h₁
    obtain ⟨J₀, hJ₀, eJ₀⟩ := exists_good M₀ hM₀ z (fun k => pt k ≫ φ) j₀ (fun _ _ _ => rfl) h₀
    have e := H J₀ J hJ₀ hJ
    rw [val_of t _ z J j (fun k => by rw [Category.id_comp]; exact eJ k),
      val_of t₀ _ z J₀ j₀ (fun k => by rw [Category.id_comp, ← eJ₀ k]; exact congrArg J₀ hp.symm), om, eJ,
      eJ₀ PUnit.unit] at e
    rw [Fintype.prod_unique]
    exact e

theorem exists_unit_basicOpen {R : Type} [CommRing R] (u : R) :
    ∃ c : Γ((TW (R := R) (PrimeSpectrum.basicOpen u)).left, ⊤)ˣ, ∀ (F : Type) [Field F] (r : R →+* F)
      (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
      z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ (p : Sp F) (n : ℤ),
      (gm z p ⊤ (c ^ n)).val = toStk p (r u ^ n) := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen u
  let s : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u
  have hc : IsUnit ((U.ι.app ⊤).hom s) := by
    apply U.toScheme.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    have : y ∈ U.toScheme.basicOpen ((U.ι.app ⊤).hom s) := by
      rw [← Scheme.preimage_basicOpen]
      show U.ι y ∈ (Spec (CommRingCat.of R)).basicOpen s
      rw [basicOpen_eq_of_affine]
      exact y.2
    exact (Scheme.mem_basicOpen _ _ y hy).1 this
  refine ⟨hc.unit, fun F _ r z hz p n => ?_⟩
  have e : (gm z p ⊤ hc.unit).val = toStk p (r u) := by
    have e₁ : (gm z p ⊤ hc.unit).val = gs (z ≫ U.ι) p ⊤ s :=
      (gs_unit z p ⊤ trivial hc.unit).symm.trans (gs_pull z U.ι p ⊤ trivial s)
    have hz' : z ≫ U.ι = specOf r := hz
    rw [e₁, hz', gs_eq _ p ⊤ trivial]
    have nat := congrArg (fun q => q.hom u) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
    exact congrArg ((Sp F).presheaf.germ ⊤ p trivial).hom nat.symm
  have h0 : r u ≠ 0 := fun h => by
    rw [h, map_zero] at e
    exact (gm z p ⊤ hc.unit).ne_zero e
  have e' : Units.map (toStk p).toMonoidHom (Units.mk0 _ h0) = gm z p ⊤ hc.unit := Units.ext e.symm
  refine (congrArg Units.val ((map_zpow (gm z p ⊤) hc.unit n).trans ((congrArg (· ^ n) e'.symm).trans
    (map_zpow _ _ n).symm))).trans ?_
  show toStk p _ = _
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem val_scale' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

variable {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {D₀ : DegPre O'} {D : DegPre R}

theorem exists_gen_on (f : O' →+* R) (u : R) {φ : D.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso D.P.L (D₀.P.L.pull φ))
    (hw : w.IsGen) (y : D₀.X) (x : D.X) (hc : (D.c x).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (hy : PsiUnitOn D₀ y Set.univ) (n : ℤ) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (K := PUnit)
        (fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) (fun _ => -1)), s.IsGen ∧
      ∀ (F : Type) [Field F] (r : R →+* F) (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
        z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ j : Sp F ⟶ (TK O').left,
        j ≫ jK O' = specOf r ≫ spMap f →
        GenRel w (LB.pullGen _ _ _ s z) (LB.pullGen _ _ _ (D₀.psi y) j) (r u ^ n) := by
  obtain ⟨t, ht, H⟩ := (psiUnitOn_univ_iff D₀ y).1 hy
  obtain ⟨c, hcu⟩ := exists_unit_basicOpen u
  have hψ : (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left ≫ φ =
      ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) ≫ (D₀.c y).left := by
    show ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (D.c x).left) ≫ φ = _
    rw [Category.assoc, hc, Category.assoc]
  obtain ⟨a, ha, va⟩ := exists_down_om hw D₀.P.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left)
    ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) (fun _ => hψ) t ht
  refine ⟨scaleGen (c ^ n) a, scaleGen_isGen _ _ ha, fun F _ r z hz j hj => ?_⟩
  have p : Sp F := (default : PrimeSpectrum F)
  have hzj : z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f = j ≫ jK O' := by
    rw [← Category.assoc, hz, hj]
  refine (genRel_iff_val D.P.isLB D₀.P.isLB w _ _ _ p).2 ⟨?_, fun J₀ J hJ₀ hJ => ?_⟩
  · show (z ≫ (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) ≫ φ = j ≫ jK O' ≫ (D₀.c y).left
    rw [Category.assoc, hψ, ← Category.assoc, hzj, Category.assoc]
  · have e := va _ z p J₀ J hJ₀ hJ
    rw [Fintype.prod_unique, hzj, ← val_pull hJ₀, val_corr hJ₀ H] at e
    rw [val_pull hJ, val_pull hJ₀, Category.id_comp, Category.id_comp, val_scale' _ _ _ hJ, e, ← hcu F r z hz p n,
      ← Units.val_mul, mul_left_comm]

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {pt pt' : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (hp : pt PUnit.unit = pt' PUnit.unit) (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x) (z : Sp F) {J} (hJ : Good M z J) :
    val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' hM₀ z
  have e := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h).2 J₀ J hJ₀ hJ
  have e' := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h').2 J₀ J hJ₀ hJ
  rw [hp, ← e'] at e
  exact mul_left_cancel (Units.ext e)

theorem corr_of_geom (U : (Spec (CommRingCat.of R)).Opens) (hU : (U : Set (Spec (CommRingCat.of R))).Nonempty)
    (x : D.X) (s : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (toUnit (TW U) ≫ D.c x).left) (fun _ => -1)))
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ z : Sp F ⟶ (TW U).left, z ≫ (TW U).hom = jFK (R := R) F ≫ jK R → ∀ p J, Good D.P.L p J →
      val s z p J = val (D.psi x) (jFK (R := R) F) p J) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ s (jK R ∣_ U)) (LB.pullGen D.P.L _ _ (D.psi x) (jK R ⁻¹ᵁ U).ι) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : Sp F ⟶ (jK R ⁻¹ᵁ U).toScheme, lam ≫ (jK R ⁻¹ᵁ U).ι = jFK (R := R) F :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem _ U hU), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ U) ≫ U.ι = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl]
  have p : Sp F := (default : PrimeSpectrum F)
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  refine TauPull.corr_of_dense D.P.isLB lam p (fun V ⟨y, hy⟩ => ?_) fun J hJ => ?_
  · rw [show lam p = y from Subtype.ext (Subsingleton.elim _ _)]
    exact hy
  · rw [val_pull hJ, val_pull hJ, hl]
    exact H _ hκ p J hJ

end GlobalTheory.ArcPsiOn

open GlobalTheory.ArcPsiOn GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem GlobalTheory.arcWit_psiOn_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : Geo.Tor.ArcIn Dm l β O' b) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (f : O' →+* R), Function.Injective f → ∀ (u : R), u ≠ 0 → ∀ (χ : Geo.Tor.Sp R ⟶ Y.X) (W : Geo.Tor.ArcWit Y a I f u χ), ∃ ψW : PsiOn W.P.D.toPre (PrimeSpectrum.basicOpen u), ∀ (F : Type) [Field F] [Algebra (FractionRing O') F] (r : R →+* F) (z : Spec (CommRingCat.of F) ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left), z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = r (f x)) → ∀ y, Geo.Tor.GenRel W.w (LB.pullGen _ _ _ (ψW.psi (W.e y)) z) (LB.pullGen _ _ _ (a.D₀.psi y) (jFK (R := O') F)) (r u ^ (a.be y y / 2)) := by
  intro E _ _ _ H Dm l Xo c O _ β Y O' _ _ b a R _ _ I f hf u hu χ W
  obtain ⟨-, s2, -, -, s5, s6⟩ := W.spec
  choose s hs H using fun x : W.P.D.toPre.X => exists_gen_on f u W.w s2 (W.e.symm x) x
    (by simpa only [LinearEquiv.apply_symm_apply] using s5 (W.e.symm x)) (a.gen _)
    (a.be (W.e.symm x) (W.e.symm x) / 2)
  refine ⟨⟨s, hs, fun x => ?_⟩, fun F _ _ r z hz hr y => ?_⟩
  · let F := AlgebraicClosure (FractionRing R)
    letI : Algebra (FractionRing O') F := ((algebraMap (FractionRing R) F).comp (fracMap hf)).toAlgebra
    have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
      congrArg (algebraMap (FractionRing R) F) (fracMap_algebraMap hf x)
    refine corr_of_geom _ ⟨⟨⊥, Ideal.isPrime_bot⟩, hu⟩ x (s x) F fun z hz p J hJ => ?_
    have hj : jFK (R := R) F ≫ jK R = specOf ((algebraMap (FractionRing R) F).comp (algebraMap R _)) :=
      (spMap_comp _ _).symm
    have k := H x F _ z (hz.trans hj) (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hF)).trans (spMap_comp f _)))
    have k' := (s6 F _ hF rfl).1 (W.e.symm x)
    rw [LinearEquiv.apply_symm_apply] at k'
    have e := val_eq_of_genRel W.P.D.toPre.P.isLB a.D₀.P.isLB (by
      show z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (W.P.D.toPre.c x).left =
        jFK (R := R) F ≫ jK R ≫ (W.P.D.toPre.c x).left
      rw [← Category.assoc, hz, Category.assoc]) k k' p hJ
    rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at e
  · have k := H (W.e y) F r z hz (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hr)).trans (spMap_comp f r)))
    rw [LinearEquiv.symm_apply_apply] at k
    exact k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoefFe
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefFE
open GlobalTheory.UT.CoefBasic

theorem coef_fe : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (h o : GtPtF D F), GtPtF.IsIota y h → o.IsZero → ∀ (w : Frm D F k h.b) (w₁ : Frm D F k o.b), w.IsGen → FrmOne w₁ → (∀ z J, Good D.P.L z J → val w (𝟙 _) z J = (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) ^ k) → ∀ (s : Fam D F k) (α : D.X), coef s o w₁ (α + k • y) = coef s h w α := by
  intro hL R _ _ D F _ _ k y h o hh ho w w₁ hw hw₁ vw s α
  obtain ⟨hb, hs⟩ := (isIota_iff _ _).1 hh
  obtain ⟨ob, os⟩ := (isZero_iff _).1 ho
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hL.1.globalFns k y α
  refine coef_eq fun z J hJ => ?_
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _ (DegPre.zF D F).left z J hJ
  have u₀ := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at u₀
  have m := val_famMult (𝟙 (TF (R := R) F)) hJ k y α
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val (D.psi y) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val D.rigK ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  rw [p₁, p₂, Over.id_left, Category.id_comp] at m
  have r : val D.rigK (jFK (R := R) F) z J = rigV D (TF (R := R) F).hom z J := val_pull hJ _ _ _
  have z₁ : lift (𝟙 (TF (R := R) F)) o.b = DegPre.zF D F := by rw [ob]; rfl
  have z₂ : DegPre.zF D F ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) h.b := by
    have a₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    have a₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, a₁, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, a₂, ← Category.assoc, a₁, Category.id_comp, _root_.one_mul]
  rw [← Over.comp_left, z₂, u₀] at e
  have t := hs α z J hJ
  rw [Category.id_comp] at t
  rw [isCoef_coef h hw α s z J hJ, z₁, e, os _ z J hJ, hw₁.2 z J hJ, t, vw z J hJ]
  have m' := congrArg Units.val m
  rw [r] at m'
  simp only [Units.val_one, _root_.mul_one, id, mul_pow, _root_.mul_assoc]
  exact congrArg₂ (· * ·) rfl m'.symm

end GlobalTheory.UT.CoefFE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisTwistField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_basis_twist_field : Laws → Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, DegPre.constBF D F (c i) _ * (b i).f j) :=
  fun _ h₂ _ _ _ D F _ _ _ hk α =>
    GlobalTheory.FamDimension.exists_basis_famSec (D := D) (F := F) h₂.secTwist hk α

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_translate_torsion_alt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → gp.b ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![eSec D.toPre.P.A, gp.b.left] (DegPre.lineε k))) (uL : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (𝟙 G * (toUnit G ≫ x)).left] ![(k : ℤ), -(k : ℤ)])) (uM : ∀ α, LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.famφB α) (fun i => (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k))), ν.IsGen ∧ uL.IsGen ∧ (∀ α, (uM α).IsGen ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (uM α) (eSec D.toPre.P.A)) (LB.mulGen D.toPre.P.L _ _ _ _ (gp.s α) ν)) ∧ ∀ (σ σ' : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α), GeneratorPullback.SecRel U.LG.L _ _ σ' _ _ σ (𝟙 G * (toUnit G ≫ x)).left _ _ uL → (∀ α, GeneratorPullback.SecRel D.toPre.P.L _ _ (f' α) _ _ (f α) (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left _ _ (uM α)) → ∀ e, U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  first | exact @GlobalTheory.expandsAt_translate_torsion | exact GlobalTheory.expandsAt_translate_torsion | (intros; apply GlobalTheory.expandsAt_translate_torsion <;> assumption)
end

