import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowJumpsAndCloudInWindowsAlongFamily
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.LetterWindows

theorem wj_eq_sz (D : D7) (j : ℕ) (ρ : D.what₂.Tau) :
    Formalism.BasicNotions.wj D j ρ = ((Formalism.MainNotions.AdmissibleParameterJ.sz D j ρ : ℚ) : ℝ) := by
  unfold Formalism.BasicNotions.wj Formalism.MainNotions.AdmissibleParameterJ.sz
  split_ifs <;> simp

theorem sz_eq (D : D7) (j : ℕ) (ρ : D.what₂.Tau) (h : j - 1 < D.R.m) :
    Formalism.MainNotions.AdmissibleParameterJ.sz D j ρ = (D.hc ρ).e ⟨j - 1, h⟩ := by
  unfold Formalism.MainNotions.AdmissibleParameterJ.sz
  rw [dif_pos h]

theorem low_abs (D : D7) (j : ℕ) (h : j - 1 < D.R.m) (up : Bool) (ρ : D.what₂.Tau) (z : ℤ)
    (hz : (z : ℚ) ∈ Formalism.MainNotions.AdmissibleParameterJ.lowT D up j ρ) :
    ∃ a : Fin D.R.m, |(z : ℝ) - ((D.R.t : ℝ) - 1) / 2| =
      |((((D.hc ρ).b a - (D.hc ρ).e ⟨j - 1, h⟩ : ℚ)) : ℝ)| := by
  cases up
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.lowT, Formalism.MainNotions.AdmissibleParameterJ.reflS, Formalism.MainNotions.AdmissibleParameterJ.lowJ, Formalism.MainNotions.AdmissibleParameterJ.refl,
      Formalism.MainNotions.AdmissibleParameterJ.c0, sz_eq D j ρ h, Set.mem_setOf_eq] at hz
    simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    congr 1
    linarith
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.lowT, Formalism.MainNotions.AdmissibleParameterJ.lowJ,
      Formalism.MainNotions.AdmissibleParameterJ.c0, sz_eq D j ρ h, Set.mem_setOf_eq, if_true] at hz
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    rw [abs_sub_comm ((((D.hc ρ).b a : ℚ)) : ℝ)]
    congr 1
    linarith

theorem cloud_val (D : D7) (j : ℕ) (up : Bool) (ρ : D.what₂.Tau) (z : ℤ)
    (hz : (z : ℚ) ∈ Formalism.MainNotions.AdmissibleParameterJ.cloudT D up j ρ) :
    ∃ a : Fin (D.R.k - 1),
      (if up then (z : ℝ) - ((D.R.t : ℝ) - 1) / 2 else ((D.R.t : ℝ) - 1) / 2 - z) =
        Formalism.BasicNotions.wj D j ρ + ((((D.hc ρ).v a : ℚ)) : ℝ) := by
  rw [wj_eq_sz]
  cases up
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.cloudT, Formalism.MainNotions.AdmissibleParameterJ.reflS, Formalism.MainNotions.AdmissibleParameterJ.cloudJ, Formalism.MainNotions.AdmissibleParameterJ.refl,
      Formalism.MainNotions.AdmissibleParameterJ.c0, Set.mem_setOf_eq] at hz
    simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    linarith
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.cloudT, Formalism.MainNotions.AdmissibleParameterJ.cloudJ,
      Formalism.MainNotions.AdmissibleParameterJ.c0, Set.mem_setOf_eq, if_true] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    linarith

theorem base_window (D : D7) (L : SizeData₂ D) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) :
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes L,
      W0 ≤ Formalism.BasicNotions.wj D j ρ ∧ Formalism.BasicNotions.wj D j ρ ≤ W0 + L.etaSz + 1 := by
  by_cases htop : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · have htop' := htop
    simp only [Formalism.BasicNotions.Host.topPlaces, Finset.mem_image] at htop'
    obtain ⟨t, ht, hte⟩ := htop'
    have hw := L.win_top j hj1 hjm ρ ⟨t, ht⟩ hte.symm
    refine ⟨(L.bT ⟨t, ht⟩ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ), ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr ⟨⟨t, ht⟩, rfl⟩)
    · have := Int.floor_le (L.sc.b' / L.sc.x)
      linarith [hw.1]
    · have := Int.lt_floor_add_one (L.sc.b' / L.sc.x)
      linarith [hw.2]
  · by_cases hthick : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces
    · have hw := L.win_thick j hj1 hjm ρ hthick
      exact ⟨L.sc.b, Or.inl rfl, hw.1, hw.2⟩
    · have hthin : D.host.IsThin (D.eTau ρ : D.R.GG) :=
        ⟨(D.eTau ρ).2, htop, hthick⟩
      have hw := L.win_thin j hj1 hjm ρ hthin
      exact ⟨L.sc.w'' D.R.n, Or.inr (Or.inl rfl), hw.1, by linarith [hw.2]⟩

end GlobalTheory.LetterWindows

namespace GlobalTheory.LetterWindows

theorem lows_cloud_windows : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x) (j : ℕ), 1 ≤ j → j ≤ (Fm.D x a).R.m →
    ∀ (up : Bool) (ρ : (Fm.D x a).what₂.Tau),
    (∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.lowT (Fm.D x a) up j ρ →
      |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
      2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
        |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a), ∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.cloudT (Fm.D x a) up j ρ →
      W0 ≤ (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
        W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1 := by
  intro eps Fm x hx a j hj1 hjm up ρ
  have h : j - 1 < (Fm.D x a).R.m := by omega
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := low_abs (Fm.D x a) j h up ρ z hz
    rw [hi]
    refine ⟨(Fm.L x a).be_close ρ i ⟨j - 1, h⟩, ?_⟩
    have := (Fm.params x hx a).lows_far ρ i ⟨j - 1, h⟩
    have e : 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) = 2 * (Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a) := by
      ring
    rw [e]
    exact this
  · obtain ⟨W0, hW0, hlo, hhi⟩ := base_window (Fm.D x a) (Fm.L x a) j hj1 hjm ρ
    refine ⟨W0, hW0, fun z hz => ?_⟩
    obtain ⟨i, hi⟩ := cloud_val (Fm.D x a) j up ρ z hz
    rw [hi]
    have hv := (Fm.L x a).cloud_v ρ i
    constructor <;> linarith [hv.1, hv.2]

end GlobalTheory.LetterWindows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

noncomputable def divBy (a : O) : O →ₗ[O] KmodO O :=
  (Submodule.mkQ _).comp ((LinearMap.mulLeft O ((algebraMap O (FractionRing O) a)⁻¹)).comp
    (Algebra.linearMap O (FractionRing O)))

theorem divBy_apply (a y : O) : divBy a y =
    Submodule.Quotient.mk ((algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y) := rfl

theorem ker_divBy {a : O} (ha : a ≠ 0) : LinearMap.ker (divBy a) = Ideal.span {a} := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  ext y
  rw [LinearMap.mem_ker, divBy_apply, Ideal.mem_span_singleton]
  refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    have hb' : algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y := hb
    rw [map_mul, hb', mul_inv_cancel_left₀ h0]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    change algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) (a * b)
    rw [map_mul, inv_mul_cancel_left₀ h0]

theorem mem_range_divBy {a : O} (ha : a ≠ 0) (x : KmodO O) (hx : a • x = 0) :
    x ∈ LinearMap.range (divBy a) := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  rw [divBy_apply]
  congr 1
  have hy' : algebraMap O (FractionRing O) y = algebraMap O (FractionRing O) a * z := by
    rw [← Algebra.smul_def]; exact hy
  rw [hy', inv_mul_cancel_left₀ h0]

theorem length_le_of_smul_eq_zero {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : Module.length O P ≤ addVal O a := by
  have hle : P ≤ LinearMap.range (divBy a) := fun x hx => mem_range_divBy ha x (hP x hx)
  let f : P →ₗ[O] O ⧸ Ideal.span {a} :=
    (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).toLinearMap.comp
      ((LinearMap.quotKerEquivRange (divBy a)).symm.toLinearMap.comp (Submodule.inclusion hle))
  have hf : Function.Injective f := by
    intro x y hxy
    have := (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).injective hxy
    have := (LinearMap.quotKerEquivRange (divBy a)).symm.injective this
    exact Submodule.inclusion_injective hle this
  calc Module.length O P ≤ Module.length O (O ⧸ Ideal.span {a}) := Module.length_le_of_injective f hf
    _ = addVal O a := Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a

theorem lenUnit_le_of_smul_eq_zero (l : ℕ) {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : lenUnit (O := O) l P ≤ lenUnit (O := O) l (O ⧸ Ideal.span {a}) := by
  unfold lenUnit
  have hne : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
    exact fun h => ha (addVal_eq_top_iff.mp h)
  have h1 : (Module.length O P).toNat ≤ (Module.length O (O ⧸ Ideal.span {a})).toNat :=
    ENat.toNat_le_toNat ((length_le_of_smul_eq_zero ha P hP).trans_eq
      (Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a).symm) hne
  gcongr

end DVR

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

theorem lenUnit_invariants_le (D : D7) (i : D.nd.Loc) (hls : D.nd.l i ∉ D.host.small)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ) (hn : 0 < n) :
    lenUnit (O := D.nd.O i) (D.nd.l i)
        ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w))) ≤
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℚ) := by
  haveI := D.nd.lPrime i
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hls
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.PtCore.EpsAll.exists_generator (GlobalTheory.EpsInertia.epsAll D i) w hw
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ hgI
  set b : (D.nd.O i)ˣ := Formalism.MainNotions.N.Glob.epsO D.nd i g with hbdef
  have hb : (b : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ 1 * ((1 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) := by
    rw [Units.val_one, mul_one, ← UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hls, ← hg]
    rfl
  set a : D.nd.O i := (b : D.nd.O i) ^ n - 1 with hadef
  have hva : addVal (D.nd.O i) a =
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℕ∞) * addVal (D.nd.O i) ((D.nd.l i : ℕ) : D.nd.O i) := by
    rw [hadef, hb]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.addVal_pow_sub_one (O := D.nd.O i) (D.nd.l i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_ne_zero D.nd i)
      (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i) 1 le_rfl (fun h => absurd h hl2) 1 n hn
  have ha0 : a ≠ 0 := by
    intro h
    have ht : addVal (D.nd.O i) a = ⊤ := by rw [h]; simp
    rw [hva] at ht
    obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
    rw [he] at ht
    exact absurd ht (by rw [← Nat.cast_mul]; exact ENat.coe_ne_top _)
  have hkill : ∀ x ∈ Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)),
      a • x = 0 := by
    intro x hx
    have hfix := (Representation.mem_invariants _ x).mp hx ⟨g, hgD⟩
    have hfix' : ((b ^ n)⁻¹ : (D.nd.O i)ˣ) • x = x := by
      have e1 : ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)) ⟨g, hgD⟩ x =
          (((b ^ (-(n : ℤ)) : (D.nd.O i)ˣ)) : D.nd.O i) • x := by
        rfl
      rw [e1] at hfix
      rw [Units.smul_def, ← zpow_natCast, ← zpow_neg]
      exact hfix
    rw [hadef, sub_smul, one_smul]
    conv_lhs => rw [← hfix']
    rw [Units.smul_def, smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul, ← Units.smul_def, hfix', sub_self]
  calc lenUnit (O := D.nd.O i) (D.nd.l i) _
      ≤ lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) :=
        lenUnit_le_of_smul_eq_zero (D.nd.l i) ha0 _ hkill
    _ = _ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.lenUnit_span D.nd i hva

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

theorem unbotD_le {m : WithBot ℚ} {c : ℚ} (h : m ≤ (c : WithBot ℚ)) (hc : 0 ≤ c) : m.unbotD 0 ≤ c := by
  cases m with
  | bot => simpa using hc
  | coe a => simpa using h

theorem one_add_padicValNat_le (l : ℕ) [Fact l.Prime] {n t : ℕ} (hn : 0 < n) (hnt : n < t) :
    1 + padicValNat l n ≤ 2 * t := by
  have h1 : l ^ padicValNat l n ≤ n := Nat.le_of_dvd hn pow_padicValNat_dvd
  have h2 : 2 ^ padicValNat l n ≤ l ^ padicValNat l n :=
    Nat.pow_le_pow_left (Fact.out : l.Prime).two_le _
  have h3 : padicValNat l n < 2 ^ padicValNat l n := Nat.lt_two_pow_self
  omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), D.nd.l i ∉ D.host.small →
    D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) →
    ((h0 D.nd i col : ℚ) : ℝ) ≤ 2 * D.R.t := by
  intro D i col hl2 _ _ hcol
  haveI := D.nd.lPrime i
  have key : h0 D.nd i col ≤ 2 * (D.R.t : ℚ) := by
    unfold h0
    refine unbotD_le ?_ (by positivity)
    apply Finset.max_le
    intro y hy
    obtain ⟨⟨w, n⟩, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw, hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hn0, hnt⟩ := Finset.mem_Ioo.mp hn
    refine WithBot.coe_le_coe.mpr ((lenUnit_invariants_le D i hl2 w (hcol w hw) n hn0).trans ?_)
    exact_mod_cast one_add_padicValNat_le (D.nd.l i) hn0 hnt
  exact_mod_cast key

end GlobalTheory.InvariantsKO
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspOfThetaSum
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ThetaSumDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

noncomputable def evHom {S : Type} [CommRing S] [_root_.IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) : Rul Xo c →+* S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)
  map_mul' f f' := evalAt_mul _ _ f f' y
  map_zero' := evalAt_zero _ _ y
  map_add' f f' := evalAt_add _ _ f f' y

noncomputable def secZero (Xo : Moduli Dw l) (c : Coeff l) : Subring (Rul Xo c) :=
  { (sec Xo c 0 0).toAddSubgroup with
    one_mem' := ⟨fun _ _ φ _ _ _ => (map_one φ).symm, fun p t _ _ _ => by
      have h0 : wchar (S := p.R) (ex Dw 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
      rw [h0, one_mul]
      rfl⟩
    mul_mem' := fun ha hb => by simpa using sec_mul Xo c 0 0 0 0 ha hb }

theorem cases_of_pow_succ {z : ℂ} {e : ℕ} (he : 0 < e) (hz : z ^ (e + 1) = z) :
    ‖z + 1 - z ^ e‖ = 1 ∧ ‖1 - (z ^ e + z ^ e)‖ = 1 := by
  by_cases h0 : z = 0
  · simp [h0, he.ne']
  · have h1 : z ^ e = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, hz, one_mul])
    have h2 : ‖z‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg z) he.ne').1 (by rw [← norm_pow, h1, norm_one])
    rw [h1]
    norm_num [h2]

theorem evR_eq_of_marked_pow [inst : Algebra c.F ℂ] (hσ : GoodEmb c (algebraMap c.F ℂ)) (hA : l.A = 1) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) {m : ℕ} (hm0 : 0 < m) (hfm : f ^ (m + 1) = f) {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} (hr : 1 ≤ r)
    (hs : IsSympl X bas) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : ∀ a, mk a ∈ L) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) {y y' : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x' L y')
    (hk : A.Marked mk) (hk' : A'.Marked mk) : evR Xo c f y = evR Xo c f y' := by
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra := ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hf' : f ∈ secZero Xo c := hf
  have hz : ∀ z : FrPt Xo c ℂ, evHom z f ^ (m + 1) = evHom z f := fun z => by rw [← map_pow, hfm]
  have e1 : ∀ z : FrPt Xo c ℂ, evR Xo c (f + 1 - f ^ m) z = evHom z f + 1 - evHom z f ^ m := fun z => by
    change evHom z _ = _
    rw [map_sub, map_add, map_one, map_pow]
  have e2 : ∀ z : FrPt Xo c ℂ, evR Xo c (1 - (f ^ m + f ^ m)) z = 1 - (evHom z f ^ m + evHom z f ^ m) := fun z => by
    change evHom z _ = _
    rw [map_sub, map_add, map_one, map_pow]
  have h1 := evR_eq_of_marked σ hσ hA (f := f + 1 - f ^ m) (show _ ∈ secZero Xo c from sub_mem (add_mem hf' (one_mem _)) (pow_mem hf' m))
    (fun z => (congrArg norm (e1 z)).trans (cases_of_pow_succ hm0 (hz z)).1) hr hs hm x hx x' hx' y y' A A' hk hk'
  have h2 := evR_eq_of_marked σ hσ hA (f := 1 - (f ^ m + f ^ m))
    (show _ ∈ secZero Xo c from sub_mem (one_mem _) (add_mem (pow_mem hf' m) (pow_mem hf' m)))
    (fun z => (congrArg norm (e2 z)).trans (cases_of_pow_succ hm0 (hz z)).2) hr hs hm x hx x' hx' y y' A A' hk hk'
  rw [e1, e1] at h1
  rw [e2, e2] at h2
  change evHom y f = evHom y' f
  linear_combination h1 - (1 / 2 : ℂ) * h2

set_option maxHeartbeats 1000000 in

theorem mem_cusp_of_thetaSum (d : DeltaDat Xo c n) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (hr1 : 1 ≤ r)
    (hU : ∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (hA : l.A = 1) (hlev : d.IsLev) (hA₂ : d.l₂.A = 1)
    [StarRing (𝓞 E)] (hnab : IsNab d.Xo₂ d.c₂ d.nab₂) (Λ : GenLat E n) (N : ℕ) (hun : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M)
    (hO : Λ.LevOK N d.l₂.M) (a : (E →+* ℂ) × ℕ → ℕ) (hD : Dom a n) (hL : LastPos Dw a)
    {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂) (m : ℕ) (hm : 0 < m) (w : T → (Fin n → LevQ Dw d.l₂) → c.F)
    (P : T → MvPolynomial (LtN Dw n) c.F) (hcs : ∀ t, cs t ∈ sec d.Xo₂ d.c₂ 0 0 ∧ cs t ^ (m + 1) = cs t)
    (hP : ∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (f : Rul Xo c) (hsec : f ∈ sec Xo c a n)
    (hval : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
      ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
        (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) Λ N
          (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
        evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t) :
    f ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  have hci := GlobalTheory.chartIndependence_unconditional
  refine (Formalism.L2.PjFree.mem_cusp Xo c U a n f).2
    ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = σ := RingHom.ext fun t => halg t
  have hσ₂ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) := by
    have h1 : d.eF (IntermediateField.inclusion c.le (baseKA l).ρ) =
        IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ := Subtype.ext rfl
    change algebraMap d.c₂.F ℂ (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = _
    rw [← h1, halg]
    exact hσ
  have hn : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k
  obtain ⟨Dc, hDe, hk⟩ := exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ShortRead.halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hΛ : Λ.La ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ.La).2.1 _ N hM hun hT hO
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.frames_isConnected E r ((U σ).X k)).nonempty
  obtain ⟨b, -, hx₀, hux₀⟩ := exists_unitFr_rmul ((U σ).X k) hx₁
  obtain ⟨A₀, hAm, -⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx₀⟩ hux₀
  obtain ⟨z₀, hz₀⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC (U σ) k ⟨_, hx₀⟩)
  obtain ⟨B₀, -, mk₂, hmk₂, hB₀, hover⟩ := Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e _ _
    _ A₀ Dc.sympl hx₀ hsd z₀ hz₀ _ hAm
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hsd hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hO.1.pos
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv
  have hpt : ∀ x (hx : x ∈ ((U σ).X k).dom), IsUnitFr ((U σ).X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib ((U σ).X k) Dc.bas Dc.idx W.e x ((U σ).X k).Λ (unC (U σ) k ⟨x, hx⟩)) (θ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC (U σ) k ⟨x, hx⟩).s θ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA ((U σ).X k) Dc.bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨A, hA, θ, hθ, hmean⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
      (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv x hx θ hT
    exact ⟨κ, hnorm x hx hux θ κ hT hmean hκ, A, θ, hA, hθ, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, -, hCe⟩ := Const.exists_const ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k) ρ hρ κ hκ
  have hG := fun j => ShortRead.sb_gphi Dc.idx Dc.sympl hn hw hw' hsd hΛ hv.1 (fun q => σ (w j q)) Y
  have hth := fun j => theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ (hG j) _ (Dc.mem _ (hP j))
  rw [Dc.wt_eq] at hth
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  let co : T → ℂ := fun j => evR d.Xo₂ d.c₂ (cs j) z₀ * algebraMap d.c₂.F ℂ
    (1⁻¹ * ((Λ.mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ * (Λ.zCard N r : d.c₂.F))
  have hrd := hCe (Formalism.L2.PjFree.rdU (U σ) f k) (fun x => ∑ j, co j * thP ((U σ).X k) Dc.hr Dc.bas Dc.idx
      (gphi ((U σ).X k) Dc.bas (H.w0 : E) Λ.La ((U σ).X k).Λ v (fun q => σ (w j q)) Y)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P j))) x) hs.1
    (DifferentiableOn.fun_sum fun j _ => (hth j).1.const_mul _) (fun x hx b hb => ⟨hs.2.1 x hx b hb, by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hth j).2.1 x hx b hb, mul_left_comm]
      rfl⟩) (by
      intro x hx hux
      obtain ⟨A, θ, hAk, hθ, hprod⟩ := hpt x hx hux
      obtain ⟨y₂, B, hy₂, hB, hrd⟩ := Reach.exists_lift_of_reached d halg hσ₂ hlev hA hA₂ hr1 A Dc.sympl hx hsd hmk hAk
        hmk₂ hover hx₀ B₀ hz₀ hB₀
      obtain ⟨vc, hvc, hev⟩ := hval ℂ halg _ y₂ hy₂
      have hrd' : Formalism.L2.PjFree.rdU (U σ) f k x = evR Xo c f (unC (U σ) k ⟨x, hx⟩) := dif_pos hx
      rw [hrd', hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hsd _ n Dc.hr Dc.eL
        hu.1 hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v _ (hrd θ hθ) hv hprod mk₂ hmk₂ hB Λ.La hΛ N hO Y hY a _
        ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP j)) _ 1 (vc j) (hvc j)
      rw [h, MvPolynomial.map_map, hcomp, evR_eq_of_marked_pow hσ₂ hA₂ (hcs j).1 hm (hcs j).2 hr1 Dc.sympl hmk₂.mem hx hx₀
        B B₀ hB hB₀]
      simp only [halg, co]
      change _ * (_ * _ * thP _ _ _ _ (gphi _ _ _ _ _ _ (fun q => σ (w j q)) _) _ _) = _
      ring)
  have hwt : Formalism.L2.PjFree.laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  rw [hwt] at hs ⊢
  refine CuspSum.mem_SS_of_eq_sum_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn Dc.k Dc.k' ?_ T
    _ _ (fun j => ShortRead.sb_smul (C * co j) (hG j)) (fun j => Dc.mem _ (hP j)) _ (fun x hx => ?_) hs.2.2
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · rw [hrd x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn (hG j) (Dc.mem _ (hP j)) hx, mul_assoc C]

end GlobalTheory.ThetaSumDescent
end

