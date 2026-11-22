import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RestrictMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0887
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTameCharacter
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType ValuativeRel Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameCharLabel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {p : ℕ} [Fact p.Prime]

theorem red_natCast_val (hp : resCard F = p) (a : ZMod p) : red hp ((a.val : ℕ) : 𝒪[F]) = a := by
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem valuation_natCast_val (hp : resCard F = p) (a : (ZMod p)ˣ) :
    valuation F ((((a : ZMod p).val : ℕ) : F)) = 1 := by
  have hu : IsUnit (((a : ZMod p).val : ℕ) : 𝒪[F]) :=
    isUnit_of_red_ne_zero hp (by rw [red_natCast_val]; exact a.ne_zero)
  have := (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.1 hu
  rwa [map_natCast] at this

theorem tame_eq {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) {x y : Fˣ} (hy : valuation F (y : F) = 1)
    (hxy : valuation F ((x : F) - y) < 1) : χ x = χ y := by
  have h1 : valuation F (((x / y : Fˣ) : F) - 1) < 1 := by
    have : ((x / y : Fˣ) : F) - 1 = ((x : F) - y) / y := by
      rw [Units.val_div_eq_div_val, sub_div, div_self y.ne_zero]
    rw [this, map_div₀, hy, div_one]
    exact hxy
  have := hχ _ h1
  rwa [_root_.map_div, div_eq_one] at this

def unitOf (hp : resCard F = p) (a : (ZMod p)ˣ) : Fˣ :=
  Units.mk0 (((a : ZMod p).val : ℕ) : F) fun h => by
    have := valuation_natCast_val hp a
    rw [h, map_zero] at this
    exact zero_ne_one this

theorem eq_unitOf {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) (hp : resCard F = p) (a : (ZMod p)ˣ) (x : Fˣ)
    (hx : valuation F ((x : F) - ((a : ZMod p).val : F)) < 1) : χ x = χ (unitOf hp a) :=
  tame_eq hχ (valuation_natCast_val hp a) hx

theorem exists_charLift (hp : resCard F = p) {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) : ∃ θ : (ZMod p)ˣ →* ℂˣ, CharLift θ χ := by
  refine ⟨{ toFun := fun a => χ (unitOf hp a), map_one' := ?_, map_mul' := fun a b => ?_ }, fun a x hx => ?_⟩
  · have h := eq_unitOf hχ hp 1 1 (by
      have := (red_eq_iff_val hp 1 ((1 : (ZMod p)ˣ) : ZMod p)).1 (by simp)
      simpa using this)
    rw [map_one] at h
    exact h.symm
  · have h := eq_unitOf hχ hp (a * b) (unitOf hp a * unitOf hp b) (by
      have := (red_eq_iff_val hp (((a : ZMod p).val : ℕ) * ((b : ZMod p).val : ℕ) : 𝒪[F]) ((a * b : (ZMod p)ˣ) : ZMod p)).1
        (by rw [map_mul, red_natCast_val, red_natCast_val, Units.val_mul])
      rw [MulMemClass.coe_mul, SubringClass.coe_natCast, SubringClass.coe_natCast] at this
      rw [Units.val_mul]
      exact this)
    rw [map_mul] at h
    exact h.symm
  · exact eq_unitOf hχ hp a x hx

end Local

end GlobalTheory.TameCharLabel

namespace GlobalTheory.TameCharLabel

open NumberField IsDedekindDomain GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel

theorem inflates_det {E : Type} [Field E] [NumberField E] {g : ℕ} [Fact g.Prime] {w : HeightOneSpectrum (𝓞 E)}
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {θ : (ZMod g)ˣ →* ℂˣ} {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hθ : CharLift θ χ) :
    Inflates ((IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  set c := Matrix.GeneralLinearGroup.det k
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c) := by
    ext; simp [c, GlobalTheory.GLp.inc, RingHom.map_det]
  have e3 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom c := by
    ext; simp [c, GlobalTheory.GLp.red, RingHom.map_det]
  set r : ℕ := (PadicInt.toZMod (c : ℤ_[g])).val
  have hk : ‖(((c : ℤ_[g]) - r : ℤ_[g]) : ℚ_[g])‖ < 1 := by
    have : (c : ℤ_[g]) - r ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    exact this
  have h6 := he.lt_one_iff_lt_one.2 (GlobalTheory.Published.DepthZeroTypeModel.v_lt_one i hi hk)
  have h7 : χ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c)) =
      θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom c) := by
    refine hθ _ _ ?_
    convert h6 using 2
    simp [r]
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, e3, h7]

theorem label_reduction : GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u := by
  intro H hL D Γ k v χ hχ u htame hlab
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hp : resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k := by
    haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨h1, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    exact (GlobalTheory.LocLanglands.resCard_eq_normV _).trans h1
  refine ⟨hp, fun L hteich hgen => ?_⟩
  obtain ⟨θ, hθ⟩ := exists_charLift hp htame
  set x := GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
    (GlobalTheory.LocLanglands.cls (IrrRep.det (Fin 1) χ hχ)) with hx
  have hlab' : GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) x = X - C u := hlab
  refine ⟨θ, hθ, fun hu0 => ?_, fun u' hu' => ?_⟩
  · have := GlobalTheory.WeilDeligne.WD.lab_coeff_zero_ne_zero (D.ntypes.teichC k) (D.ntypes.tg k v) x
    rw [hlab', hu0] at this
    simp at this
  · obtain ⟨I⟩ := GlobalTheory.TypeIdent.nonempty_ident D
    obtain ⟨P, hP, hPe⟩ := exists_label L θ u' hu'
    have hT : Formalism.L2.NT.TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (Γ.kv k v) (D.ntypes.tg k v) L.gen := by
      rw [hgen]; exact Γ.tg_tame k v
    have h1 := H D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
      (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL _) (I.i k v) (I.cont k v) (Γ.kv k v) L _ (D.ntypes.tg_mem k v) hT 1
      (IrrRep.det (Fin 1) χ hχ) (GlobalTheory.LocGL.IrrGL.isCusp_ofChar χ hχ) (tauOne θ) P hP
      (inflates_det (I.i k v) (I.cont k v) hχ hθ)
    rw [hPe] at h1
    obtain ⟨a, ha, ε, -, hl⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
    have hdim : x.lpDim = 1 := hl.dim _
    have h2 := GlobalTheory.WeilDeligne.WD.inePol_eq_of_natDegree_lab (D.ntypes.teichC k) (D.ntypes.tg k v) x
      (by rw [hlab', hdim, natDegree_X_sub_C])
    have hr : Formalism.CyclotomicNorms.rootsBar (X - C u) = {algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) u} := by
      simp [Formalism.CyclotomicNorms.rootsBar]
    rw [hlab', hr, h1] at h2
    have h3 := congrArg (fun q => q.coeff 0) h2
    simp at h3
    rw [hteich]
    exact h3
end GlobalTheory.TameCharLabel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDZOfSplitReg
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroAssembly

open GlobalTheory.WeilDeligne (WD Weil ineIncl TeichmullerInertiaLabelCondition Wild Wild_le_Ine)
open GlobalTheory.SplitRead.BlockParam (charPol_lpChar_of_unr twistIrr)

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} {g : ℕ} [Fact g.Prime]

theorem lab_lpChar_of_unr (τ : AlgebraicClosure (ZMod g) →* ℂ) (γ : G E Ω) (x χ : WD h) (hx : x.unr)
    (hd : χ.lpDim = 1) (u : ZMod g) (hχ : WD.lab τ γ χ = X - C u) :
    WD.lab τ γ (x.lpChar χ) = (X - C u) ^ x.lpDim := by
  have H : TeichmullerInertiaLabelCondition B w τ γ := by
    by_contra H
    rw [WD.lab_of_not H] at hχ
    have := congrArg natDegree hχ
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact zero_ne_one this
  have htχ : WD.tame χ := WD.tame_of_natDegree_lab (by rw [hχ, natDegree_X_sub_C, hd])
  have hc1 : ∀ σ : Ine (F := E) B, (σ : G E Ω) ∈ Wild E B → χ.charPol (ineIncl h σ) = X - C 1 := by
    intro σ hσ
    have := (WD.tame_iff_inePol χ).1 htχ σ hσ
    rw [WD.inePol_of_mem_Ine _ σ.2, hd, pow_one] at this
    rw [C_1]; exact this
  have hdim : (x.lpChar χ).lpDim = x.lpDim := by
    obtain ⟨σ, hσ⟩ : ∃ σ : Ine (F := E) B, (σ : G E Ω) ∈ Wild E B := ⟨1, (Wild E B).one_mem⟩
    have h1 := charPol_lpChar_of_unr x χ hx σ 1 (hc1 σ hσ)
    rw [← WD.charPol_natDegree (x.lpChar χ) (ineIncl h σ), h1, natDegree_pow, natDegree_X_sub_C, mul_one]
  have ht : WD.tame (x.lpChar χ) := by
    rw [WD.tame_iff_inePol]
    intro σ hσ
    rw [WD.inePol_of_mem_Ine _ (Wild_le_Ine hσ), hdim,
      charPol_lpChar_of_unr x χ hx ⟨σ, Wild_le_Ine hσ⟩ 1 (hc1 ⟨σ, Wild_le_Ine hσ⟩ hσ), C_1]
  set p := χ.charPol (ineIncl h ⟨γ, H.2.1⟩) with hp
  have hpm : p.Monic := WD.charPol_monic _ _
  have hpd : p.natDegree = 1 := by rw [hp, WD.charPol_natDegree, hd]
  have hpe : p = X - C (-p.coeff 0) := by rw [map_neg, sub_neg_eq_add]; exact hpm.eq_X_add_C hpd
  have hχ' := (WD.lab_eq_iff_of_tame H htχ).1 hχ
  have hr1 := WD.rootsBar_X_sub_C_pow u 1
  rw [pow_one, one_nsmul] at hr1
  rw [WD.inePol_of_mem_Ine _ H.2.1, ← hp, hpe, roots_X_sub_C, hr1,
    Multiset.map_singleton, Multiset.singleton_inj] at hχ'
  rw [WD.lab_eq_iff_of_tame H ht, WD.inePol_of_mem_Ine _ H.2.1,
    charPol_lpChar_of_unr x χ hx ⟨γ, H.2.1⟩ (-p.coeff 0) (hpe ▸ rfl), roots_pow, roots_X_sub_C,
    WD.rootsBar_X_sub_C_pow, Multiset.map_nsmul, Multiset.map_singleton, hχ'.2]
  exact ⟨(monic_X_sub_C u).pow _, rfl⟩

end Local

end GlobalTheory.DepthZeroAssembly

namespace GlobalTheory.DepthZeroAssembly

open GlobalTheory.WeilDeligne (WD)
open GlobalTheory.SplitRead.BlockParam (twistIrr)

theorem locDZ_of_split_reg : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), SplitLoc hL D → RegLoc hL D → LocDZ hL D := by
  intro hL D hS hR k v χ hχ u π ρ f ht hlab hser hsq hnr hx
  obtain ⟨π₁, π₂, hsph, e, y, hy1, hy2⟩ := hS k v χ hχ u π ρ f ht hlab hser hnr hx
  obtain ⟨hm1, hl1⟩ := hR k v π₁ ρ f hser hsq ⟨y, hy1, hy2⟩
  have L : RecLaws (rcAt hL D (D.naut.plGw k v)) :=
    (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))).recLaws
  have e' : Nonempty (π.π.Equiv (GlobalTheory.SmGL.prod₂ π₁.π (twistIrr π₂ χ hχ).π)) := e
  have e1 := L.prod D.R.r D.R.t π₁ (twistIrr π₂ χ hχ) π e'
  have e2 := L.twist D.R.t χ (Irr.ofDet 1 χ hχ) π₂ (twistIrr π₂ χ hχ) ⟨.refl _⟩ ⟨.refl _⟩
  have hu := (L.sph _ π₂).2 hsph
  refine ⟨?_, ?_⟩
  · rw [e1, WD.monomial_sum_iff, e2, WD.monomial_char_iff _ _ (L.dim _ _)]
    exact ⟨hm1, WD.unr_mono0 _ hu⟩
  · unfold labAt at hl1 hlab ⊢
    rw [e1, WD.lab_lpSum, e2, lab_lpChar_of_unr _ _ _ _ hu (L.dim _ _) u hlab, hl1, L.dim]

end GlobalTheory.DepthZeroAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ComplexConjugate

namespace GlobalTheory.RSnmUnf

def padNat {m n : ℕ} (l : Fin m → ℕ) : Fin n → ℕ := fun i => if h : (i : ℕ) < m then l ⟨i, h⟩ else 0

theorem padNat_zero {m n : ℕ} : padNat (m := m) (n := n) 0 = 0 := by
  funext i; simp only [padNat, Pi.zero_apply]; split_ifs <;> rfl

open Classical in

def rsTermNM (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) (v : Fin m → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (padNat fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def uIntNM {m n : ℕ} (hmn : m + 1 ≤ n) (F : (Fin (m + 1) → Ad E) → ℂ) (φ : GA E n → ℂ) (φ' : GA E (m + 1) → ℂ)
    (x : ℝ) (h : GA E (m + 1)) : ℂ :=
  whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL hmn h) * conj (whit φ' h) * GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h) *
    ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ ((x : ℂ) - ((n : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)

end GlobalTheory.RSnmUnf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionEmptySecondIsSubquotientFirst
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) : Fin (c false) ≃ Fin r :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

theorem mem_parab_all {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : g ∈ parab R f := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  cases a with
  | false => exact absurd hab (by cases b <;> decide)
  | true => exact absurd i.2 (by omega)

theorem eq_one_true {R : Type} [CommRing R] (hc : c true = 0) (h : GL (Fin (c true)) R) : h = 1 :=
  Units.ext (Matrix.ext fun i _ => (Fin.cast hc i).elim0)

def levi {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) :
    GL (Fin r) R →* Levi R (fun j => Fin (c j)) :=
  (leviProj R f).comp ((MonoidHom.id _).codRestrict (parab R f) (mem_parab_all f hc))

theorem levi_false {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : levi f hc g false = reix R (falseEquiv f hc).symm g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi F (fun j => Fin (c j))) :
    deltaHalf F (fun j => Fin (c j)) g = 1 := by
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    rw [eq_one_true hc (g true), map_one]
  rw [h1, h2]
  simp

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evOne (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) :
    (parInd f ρ).IntertwiningMap (ρ.comp (levi f hc)) where
  toLinearMap :=
    { toFun := fun x => x.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    show x.1.1 (1 * g) = ρ (levi f hc g) (x.1.1 1)
    have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
    rw [mul_one] at this
    rw [one_mul, this, deltaHalf_eq_one hc, Units.val_one, one_smul]
    rfl

theorem evOne_apply (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) (x : IndSp f ρ) :
    evOne f hc ρ x = x.1.1 1 := rfl

theorem evOne_injective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) : Function.Injective (evOne f hc ρ) := by
  refine (injective_iff_map_eq_zero (evOne f hc ρ)).2 fun x hx => ?_
  rw [evOne_apply] at hx
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
  rw [mul_one] at this
  show x.1.1 g = 0
  rw [this, hx, map_zero, smul_zero]

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_smul_eq (hc : c true = 0) (σ : IrrRep (GL (Fin (c true)) F)) {z : σ.V} (hz : z ≠ 0)
    (y : σ.V) : ∃ a : ℂ, a • z = y := by
  let S : Subrepresentation σ.ρ := ⟨ℂ ∙ z, fun g v hv => by
    rw [eq_one_true hc g, map_one]
    exact hv⟩
  haveI := σ.irr
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have : z ∈ S.toSubmodule := Submodule.mem_span_singleton_self z
    rw [h] at this
    exact hz this
  · have : y ∈ S.toSubmodule := by rw [h]; trivial
    exact Submodule.mem_span_singleton.1 this

def tensorMap (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) :
    Representation.IntertwiningMap
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) (s false).V)
      ((piTensor fun j => (s j).ρ).comp (levi f hc)) where
  toLinearMap := (PiTensorProduct.tprod ℂ).toLinearMap x₀ false
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      MultilinearMap.toLinearMap_apply, piTensor_tprod]
    congr 1
    funext j
    cases j with
    | false => simp [levi_false]
    | true => simp [eq_one_true hc (levi f hc g true)]

theorem tensorMap_surjective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) (hx : x₀ true ≠ 0) :
    Function.Surjective (tensorMap f hc s x₀) := by
  show Function.Surjective (tensorMap f hc s x₀).toLinearMap
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := exists_smul_eq hc (s true) hx (y true)
  refine ⟨a • y false, ?_⟩
  have e1 : y = Function.update (Function.update x₀ false (y false)) true (a • x₀ true) := by
    funext j
    cases j <;> simp [ha]
  show (PiTensorProduct.tprod ℂ).toLinearMap x₀ false (a • y false) = PiTensorProduct.tprod ℂ y
  rw [map_smul, MultilinearMap.toLinearMap_apply]
  conv_rhs => rw [e1, MultilinearMap.map_update_smul]
  congr 2
  funext j
  cases j <;> simp

theorem isSubquotient_multiProd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false),
      IsSubquotient (multiProd f fun j => (s j).ρ)
        ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  intro F _ _ _ _ r c f s hc
  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨z, hz⟩ := exists_ne (0 : (s true).V)
  let x₀ : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) 0 z j
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  exact (IsSubquotient.of_injective (evOne f hc _) (evOne_injective f hc _)).trans
    (IsSubquotient.of_surjective (tensorMap f hc s x₀) (tensorMap_surjective f hc s x₀ hz))

end GlobalTheory.EmptySecondBlockProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  first | (exact @GlobalTheory.ZEulLocal.localTerm_eq) | (exact GlobalTheory.ZEulLocal.localTerm_eq) | (intros; apply GlobalTheory.ZEulLocal.localTerm_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RtMemIsoTyp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsType

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (h : GAf L n)
    (f : GAf L n → W) (hf : f ∈ NG.isoTyp ρ S) : NG.rt L n h f ∈ NG.isoTyp ρ S := by
  have hle : NG.isoTyp ρ S ≤ (NG.isoTyp ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun U hU => ?_
    intro a ha
    have hU' : U ≤ NG.isoTyp ρ S := le_sSup hU
    exact hU' (hU.1.1.stable h a ha)
  exact hle hf

theorem main : ∀ (D : D7) (M : MtFam D), AVTied D M → CenReal D M → OnMtPreservesTypeV D := by
  intro D M A hC i PI z F hF
  by_cases hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  · obtain ⟨L, -, hL⟩ := hC (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2
    rw [NTypes.onMt, dif_pos hz]
    rw [A.typeV, Submodule.mem_comap] at hF ⊢
    have e : (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) ⟨z, hz⟩ F) =
        actSum D L z ((M.loc i).real F) := hL ⟨z, hz⟩ F
    rw [e]
    unfold actSum Finsupp.sum
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (rt_mem_isoTyp _ _ _ _ hF)
  · rw [NTypes.onMt, dif_neg hz]
    exact Submodule.zero_mem _

end GlobalTheory.CenKeepsType
end

