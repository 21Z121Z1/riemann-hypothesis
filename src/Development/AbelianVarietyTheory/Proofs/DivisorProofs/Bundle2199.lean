import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
section
set_option autoImplicit false
noncomputable section
open Module

namespace GlobalTheory.PolExistsRing

theorem mem_of_annihilates {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (ψ : LinearMap.BilinForm R V) [hψ : ψ.IsPerfPair] (W W' : Submodule R V) (hc : IsCompl W W')
    [Module.Finite R W'] [Module.Projective R W'] [Module.Finite R (Dual R W)]
    [Module.Projective R (Dual R W)]
    (hrk : ∀ p : PrimeSpectrum R, rankAtStalk W' p = rankAtStalk (Dual R W) p)
    (hiso : ∀ f ∈ W, ∀ g ∈ W, ψ f g = 0) (f : V) (hf : ∀ g ∈ W, ψ f g = 0) : f ∈ W := by
  let Φ : W' →ₗ[R] Dual R W := W.subtype.dualMap ∘ₗ ψ ∘ₗ W'.subtype
  let e := Submodule.prodEquivOfIsCompl W W' hc
  have hdec : ∀ v : V, (((e.symm v).1 : W) : V) + ((e.symm v).2 : V) = v := fun v ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' W W' hc, LinearEquiv.apply_symm_apply]
  have hΦ' : ∀ v : V, ∀ g : W, Φ (e.symm v).2 g = ψ v g := by
    intro v g
    have h := congrArg (fun u ↦ ψ u g) (hdec v)
    simp only [map_add, LinearMap.add_apply] at h
    rw [hiso _ (Submodule.coe_mem _) g g.2, zero_add] at h
    simpa [Φ] using h
  have hΦ : Function.Surjective Φ := by
    intro l
    obtain ⟨v, hv⟩ := hψ.bijective_left.2 (l ∘ₗ W.projectionOnto W' hc)
    refine ⟨(e.symm v).2, LinearMap.ext fun g ↦ ?_⟩
    rw [hΦ' v g, hv]
    simp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Φ LinearMap.id hΦ
  have hsinj : Function.Injective s := fun x y h ↦ by
    have := congrArg Φ h
    rwa [← LinearMap.comp_apply, hs, ← LinearMap.comp_apply, hs] at this
  have hc2 : IsCompl (LinearMap.range s) (LinearMap.ker Φ) := by
    have h := LinearMap.isCompl_of_proj (f := s.rangeRestrict ∘ₗ Φ) (fun x ↦ by
      obtain ⟨_, y, rfl⟩ := x
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply]
      rw [← LinearMap.comp_apply Φ s, hs, LinearMap.id_apply])
    have hk : LinearMap.ker s.rangeRestrict = ⊥ := by
      rw [LinearMap.ker_rangeRestrict]; exact LinearMap.ker_eq_bot.2 hsinj
    rwa [LinearMap.ker_comp_of_ker_eq_bot _ hk] at h
  let ep := Submodule.prodEquivOfIsCompl _ _ hc2
  let es : Dual R W ≃ₗ[R] LinearMap.range s := LinearEquiv.ofInjective s hsinj
  haveI : Module.Finite R (LinearMap.range s) := Module.Finite.equiv es
  haveI : Module.Projective R (LinearMap.range s) := Module.Projective.of_equiv es
  let pr : W' →ₗ[R] LinearMap.ker Φ := LinearMap.snd R _ _ ∘ₗ ep.symm.toLinearMap
  have hpr : pr ∘ₗ (LinearMap.ker Φ).subtype = LinearMap.id := LinearMap.ext fun x ↦ by
    simp [pr, ep, Submodule.prodEquivOfIsCompl_symm_apply_right]
  haveI : Module.Finite R (LinearMap.ker Φ) :=
    Module.Finite.of_surjective pr (fun x ↦ ⟨x, by simpa using congrArg (fun m ↦ m x) hpr⟩)
  haveI : Module.Projective R (LinearMap.ker Φ) := Module.Projective.of_split _ _ hpr
  have hr0 : rankAtStalk (R := R) (LinearMap.ker Φ) = 0 := by
    have h1 := rankAtStalk_eq_of_equiv ep
    rw [rankAtStalk_prod, rankAtStalk_eq_of_equiv es.symm] at h1
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    rw [hrk p] at this
    simp only [Pi.zero_apply]
    omega
  haveI := (rankAtStalk_eq_zero_iff_subsingleton).1 hr0
  have hb : (e.symm f).2 ∈ LinearMap.ker Φ := LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ by
    rw [hΦ' f g]; exact hf g g.2)
  have h0 : (e.symm f).2 = 0 := by
    have := Subsingleton.elim (⟨_, hb⟩ : LinearMap.ker Φ) 0
    simpa using congrArg Subtype.val this
  rw [← hdec f, h0]
  simp

theorem mem_of_annihilates_dual {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ψ : LinearMap.BilinForm R (Dual R M)) [ψ.IsPerfPair] (F N : Submodule R M) (hc : IsCompl F N)
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R F] [Module.Projective R F] (g : ℕ)
    (hM : ∀ p : PrimeSpectrum R, rankAtStalk M p = 2 * g)
    (hF : ∀ p : PrimeSpectrum R, rankAtStalk F p = g)
    (hiso : ∀ f ∈ F.dualAnnihilator, ∀ h ∈ F.dualAnnihilator, ψ f h = 0) (f : Dual R M)
    (hf : ∀ h ∈ F.dualAnnihilator, ψ f h = 0) : f ∈ F.dualAnnihilator := by
  let e := Submodule.prodEquivOfIsCompl F N hc
  have hdec : ∀ x : M, (((e.symm x).1 : F) : M) + ((e.symm x).2 : M) = x := fun x ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' F N hc, LinearEquiv.apply_symm_apply]
  have hc' : IsCompl F.dualAnnihilator N.dualAnnihilator := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro φ ⟨h1, h2⟩
      rw [Submodule.mem_bot]
      refine LinearMap.ext fun x ↦ ?_
      rw [← hdec x, map_add, (Submodule.mem_dualAnnihilator _).1 h1 _ (Submodule.coe_mem _),
        (Submodule.mem_dualAnnihilator _).1 h2 _ (Submodule.coe_mem _)]
      simp
    · rw [codisjoint_iff_le_sup]
      intro φ _
      rw [Submodule.mem_sup]
      refine ⟨φ ∘ₗ N.subtype ∘ₗ LinearMap.snd R F N ∘ₗ e.symm.toLinearMap, ?_,
        φ ∘ₗ F.subtype ∘ₗ LinearMap.fst R F N ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine LinearMap.ext fun x ↦ ?_
        conv_rhs => rw [← hdec x]
        simp [add_comm]
  let eW' : Dual R F ≃ₗ[R] N.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl N F hc.symm).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator N)
  let eW : Dual R N ≃ₗ[R] F.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl F N hc).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator F)
  have hpN : (N.projectionOnto F hc.symm) ∘ₗ N.subtype = LinearMap.id :=
    LinearMap.ext fun x ↦ Submodule.projectionOnto_apply_left hc.symm x
  haveI : Module.Projective R N := Module.Projective.of_split _ _ hpN
  haveI : Module.Finite R N := Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc.symm)
  let eN : Dual R F.dualAnnihilator ≃ₗ[R] N := eW.dualMap.trans (Module.evalEquiv R N).symm
  haveI : Module.Finite R N.dualAnnihilator := Module.Finite.equiv eW'
  haveI : Module.Projective R N.dualAnnihilator := Module.Projective.of_equiv eW'
  haveI : Module.Finite R (Dual R F.dualAnnihilator) := Module.Finite.equiv eN.symm
  haveI : Module.Projective R (Dual R F.dualAnnihilator) := Module.Projective.of_equiv eN.symm
  refine mem_of_annihilates ψ _ _ hc' (fun p ↦ ?_) hiso f hf
  rw [← rankAtStalk_eq_of_equiv eW', rankAtStalk_eq_of_equiv eN, GlobalTheory.TopExt.rankAtStalk_dual F p, hF p]
  have h1 := congrFun (rankAtStalk_eq_of_equiv e) p
  rw [rankAtStalk_prod, Pi.add_apply, hM p, hF p] at h1
  omega

end GlobalTheory.PolExistsRing

namespace GlobalTheory.PolExistsRing

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo S _ x A _ π hπ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 S A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso S ⊥ (dp0 S) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 S) (𝟙 _) A
    rw [show prim (dp0 S) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 S) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by
      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 S) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (GlobalTheory.PolExists.isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 S A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, hproj, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, ⟨N, hN⟩, hFfin, hFproj, hFrk⟩ := P.2.1 S A _ hA gA
  exact mem_of_annihilates_dual (wedgeForm (dp0 S) (𝟙 _) A a' b') (PrimitiveSubmodule A) N hN _ hrk hFrk hiso f hf

end GlobalTheory.PolExistsRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScal
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

theorem mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) (n : ℕ) :
    r ∈ w.asIdeal ^ n ↔ (n : ℤ) ≤ vAdd w (r : K) := by
  have h0 : w.intValuation r ≠ 0 := w.intValuation_ne_zero r hr
  rw [← w.intValuation_le_pow_iff_mem, vAdd, HeightOneSpectrum.valuation_of_algebraMap]
  conv_lhs => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp]
  omega

theorem vAdd_div (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x / y) = vAdd w x - vAdd w y := by
  have hx' : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [vAdd, vAdd, vAdd, map_div₀, WithZero.log_div hx' hy']
  ring

end GlobalTheory.RefSum.ScalApprox

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

theorem exists_scal : ∀ (K : Type) [Field K] [NumberField K] (ρ : HeightOneSpectrum (𝓞 K) → ℝ),
    (Function.support ρ).Finite → ∀ w : HeightOneSpectrum (𝓞 K), ∃ a : K, a ≠ 0 ∧
      (vAdd w a : ℝ) = -(⌊ρ w⌋ : ℝ) ∧ ∀ w', 0 ≤ (vAdd w' a : ℝ) + ρ w' := by
  intro K _ _ ρ hρ w
  classical
  set S : Finset (HeightOneSpectrum (𝓞 K)) := insert w hρ.toFinset with hS

  have hne : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : 𝓞 K, e ∈ v.asIdeal ∧ e ≠ 0 := fun v =>
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose e he he0 using hne
  set N : ℕ := ∑ v ∈ S, (⌊ρ v⌋).toNat with hN
  set c : 𝓞 K := (∏ v ∈ S, e v) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => he0 v)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hcS : ∀ v ∈ S, -⌊ρ v⌋ + vAdd v (c : K) ≥ 0 := by
    intro v hv
    have h1 : ∏ u ∈ S, e u ∈ v.asIdeal := by
      obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem e hv
      rw [ht]; exact Ideal.mul_mem_right _ _ (he v)
    have h2 : c ∈ v.asIdeal ^ N := Ideal.pow_mem_pow h1 N
    have h3 := (mem_pow_iff v hc0 N).1 h2
    have h4 : (⌊ρ v⌋).toNat ≤ N := Finset.single_le_sum (f := fun u => (⌊ρ u⌋).toNat)
      (fun _ _ => Nat.zero_le _) hv
    have h5 : ⌊ρ v⌋ ≤ ((⌊ρ v⌋).toNat : ℤ) := Int.self_le_toNat _
    omega
  have hfc := GlobalTheory.FlatLine.finite_vAdd hcK
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ hfc.toFinset with hT
  set E : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (-⌊ρ v⌋ + vAdd v (c : K)).toNat with hE
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπpow : ∀ n : ℕ, w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := fun n => by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have hwT : w ∈ T := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v => v.asIdeal) (fun v => if v = w then E w + 1 else E v)
    (fun v _ => v.prime) (fun v _ u _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 K)) = w then π ^ E w else 0)
  have hbw := hb w hwT
  simp only [if_true] at hbw
  have hπE : π ^ E w ∈ w.asIdeal ^ E w := (w.intValuation_le_pow_iff_mem _ _).1 (le_of_eq (hπpow _))
  have hπE1 : π ^ E w ∉ w.asIdeal ^ (E w + 1) := by
    rw [← w.intValuation_le_pow_iff_mem, hπpow, WithZero.exp_le_exp]
    push_cast; omega
  have hbw1 : b ∈ w.asIdeal ^ E w := by
    have := Ideal.pow_le_pow_right (I := w.asIdeal) (Nat.le_succ (E w)) hbw
    simpa using add_mem this hπE
  have hbw2 : b ∉ w.asIdeal ^ (E w + 1) := fun h => hπE1 (by simpa using sub_mem h hbw)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbw2 (Submodule.zero_mem _)
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have hvw : vAdd w (b : K) = E w := by
    have h1 := (mem_pow_iff w hb0 _).1 hbw1
    have h2 := mt (mem_pow_iff w hb0 (E w + 1)).2 hbw2
    push_cast at h2; omega
  have hball : ∀ v, (E v : ℤ) ≤ vAdd v (b : K) := by
    intro v
    by_cases hv : v ∈ T
    · by_cases hvw' : v = w
      · subst hvw'; rw [hvw]
      · have := hb v hv
        simp only [hvw', if_false, sub_zero] at this
        exact (mem_pow_iff v hb0 _).1 this
    · have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
      have hρv : ρ v = 0 := by
        by_contra h; exact hvS (Finset.mem_insert_of_mem (hρ.mem_toFinset.2 h))
      have hcv : vAdd v (c : K) = 0 := by
        by_contra h
        exact hv (Finset.mem_union_right _ (hfc.mem_toFinset.2 (by simpa using h)))
      have : E v = 0 := by simp [hE, hρv, hcv]
      rw [this]; exact (mem_pow_iff v hb0 0).1 (by simp)
  refine ⟨(b : K) / c, div_ne_zero hbK hcK, ?_, fun v => ?_⟩
  · rw [vAdd_div w hbK hcK, hvw]
    have := hcS w (Finset.mem_insert_self _ _)
    have h6 : ((E w : ℕ) : ℤ) = -⌊ρ w⌋ + vAdd w (c : K) := Int.toNat_of_nonneg this
    rw [h6]; push_cast; ring
  · rw [vAdd_div v hbK hcK]
    have h1 := hball v
    have h2 : -⌊ρ v⌋ + vAdd v (c : K) ≤ ((E v : ℕ) : ℤ) := Int.self_le_toNat _
    have h3 : -⌊ρ v⌋ ≤ vAdd v (b : K) - vAdd v (c : K) := by omega
    have h4 : (⌊ρ v⌋ : ℝ) ≤ ρ v := Int.floor_le _
    have h5 : ((-⌊ρ v⌋ : ℤ) : ℝ) ≤ ((vAdd v (b : K) - vAdd v (c : K) : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h5 ⊢
    linarith

end GlobalTheory.RefSum.ScalApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.CovTop.SupImage

theorem linearIndependent_of_form {K L V : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module L V]
    [IsScalarTower K L V] {S : Submodule K V} {n : ℕ} {b : Fin n → V} (hK : LinearIndependent K b)
    (hS : Submodule.span K (Set.range b) = S) (hL : LinearIndependent L b) {ι : Type} {c : ι → S}
    (hc : LinearIndependent K c) : LinearIndependent L fun k => (c k : V) := by
  subst hS
  let B := (Module.Basis.span hK).baseChange L
  let φ : L ⊗[K] Submodule.span K (Set.range b) →ₗ[L] V := (Submodule.span K (Set.range b)).subtype.liftBaseChange L
  have hB : φ ∘ B = b := by
    funext k
    simp [B, φ, Module.Basis.span_apply]
  have hφ : Function.Injective φ :=
    LinearMap.injective_of_linearIndependent (by rw [B.span_eq]) (hB ▸ hL)
  have h1 : LinearIndependent L fun k => (1 : L) ⊗ₜ[K] c k := Module.Flat.linearIndependent_one_tmul hc
  have h2 := h1.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have h3 : (φ ∘ fun k => (1 : L) ⊗ₜ[K] c k) = fun k => (c k : V) := by
    funext k
    simp [φ]
  exact h3 ▸ h2

set_option maxHeartbeats 1000000 in

theorem exists_emb_image_latW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), ∃ ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL), (∀ (f : VK fw i), ∃ h : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ι f = ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) ∧ (∀ (n : ℕ) (b : Fin n → VK fw i), LinearIndependent T.Q.c.F b → LinearIndependent D.what₂.LL (fun k => ι (b k))) ∧ ι '' (latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) : Set (VK fw i)) = ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i
  have hE : VK fw i = T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := cuspW_wtZ _ _
  let e : VK fw i ≃ₗ[T.Q.c.F] (R.FW i).WK := (LinearEquiv.ofEq _ _ hE).trans (fw.e i)
  have he : ∀ f : VK fw i, e f = fw.e i ⟨f, hE ▸ f.2⟩ := fun _ => rfl
  let ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
    { toFun := fun f => (e f : Fin (R.nW i) → D.what₂.LL)
      map_add' := fun f g => by rw [map_add]; rfl
      map_smul' := fun a f => by rw [map_smul, algebraMap_smul]; rfl }
  have key : ∀ f : VK fw i, f ∈ latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) ↔ ι f ∈ (R.FW i).MK := fun f => by
    have en := fun la y => fw.nrm_eq i la y ⟨f.1, hE ▸ f.2⟩
    constructor
    · intro hf
      refine ⟨(e f).2, fun la y => (en la y).trans_le ?_⟩
      exact (T.nrmM_le_one_iff _ la _ _).2 (hf la _ (fw.pt i la y).2)
    · rintro ⟨_, hf⟩ la v hv
      obtain ⟨y, hy⟩ := (fw.pt i la).surjective ⟨v, hv⟩
      have h2 := (en la y).symm.trans_le (hf la y)
      rw [hy] at h2
      exact (T.nrmM_le_one_iff _ la ⟨v, hv⟩ _).1 h2
  refine ⟨ι, fun f => ⟨hE ▸ f.2, rfl⟩, fun n b hb => ?_, ?_⟩
  · obtain ⟨m, c, -, h1, h2, h3, -⟩ := fw.ks i
    exact linearIndependent_of_form h1 h2 h3 (hb.map' e.toLinearMap e.ker)
  · ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (key f).1 hf
    · intro hx
      obtain ⟨f, hf⟩ := e.surjective ⟨x, hx.1⟩
      have hx' : ι f = x := congrArg Subtype.val hf
      exact ⟨f, (key f).2 (hx' ▸ hx), hx'⟩

end GlobalTheory.CovTop.SupImage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortPhi

theorem exists_shortBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  intro E _ _ _ H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  let := H.starRing
  let := io.toAlgebra
  obtain ⟨Q', β, hQ', h0, hβ, hβ2, -⟩ :=
    GlobalTheory.ValForm.main E H T.V C.I.G P ϖ hϖ (IsCMField.complexConj E : E → E) fun _ => rfl
  obtain rfl : Q = Q' := funext fun χ => QForm.QVal_unique hϖ P.D (hQ χ) (hQ' χ)
  have hφ' : HasPhi y (Formalism.MainNotions.ModuliIntegralCharts.phiC _ β) := ⟨C.I.G, C.I.t', C.I.m1, C.I.m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ2, rfl⟩
  have hnn := hφ.nonneg
  obtain rfl : φ = Formalism.MainNotions.ModuliIntegralCharts.phiC _ β := (hasPhi_exists_ext_and_unique E H Dw l Xo c).2 T io y _ _ hφ hφ'
  obtain ⟨ρ, hρ, -, hq⟩ := GlobalTheory.ToricRank.rank_le_signature E H Dw l Xo T.V C.I.G P C.I.t' C.I.m2 y.1.x C.I.m1
    inferInstance
  have hrt : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
    rw [← H.bar_eq, HostModel.bar_rt]; simp
  have hw : (H.w0 : E) + IsCMField.complexConj E (H.w0 : E) = 1 := by
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      simpa only [map_mul, map_add, map_one, map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    have h3 := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add, map_one, map_ofNat, hrt] at h3
    linear_combination (h2 + h3) / 2
  have hne : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra! h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hpos := QForm.gram_posDef hϖ P.D hQ (Module.finBasis ℤ P.D.toPre.X)
  obtain ⟨b, h1, h2⟩ := gram_form_phi_holds E (IsCMField.complexConj E : E → E)
    (fun ψ z => IsCMField.complexEmbedding_complexConj E ψ z) hne H.w0 hw P.D.toPre.X β
    ⟨_, inferInstance, Module.finBasis ℤ P.D.toPre.X, by simpa only [hβ] using hpos⟩
  refine ⟨Module.finrank ℤ P.D.toPre.X, ?_, by positivity, b, fun j => ?_, fun j z => ?_⟩
  · rw [hρ]
    exact Nat.mul_le_mul (Nat.mul_div_le _ _) hq
  · have := h1 j
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero] at this
  · have := h2 j z
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero, hβ] at this

end GlobalTheory.ShortPhi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRing
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback_ring {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR S ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR S) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionNonvanishingOfBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange | exact GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange | (intros; apply GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange <;> assumption)
end

