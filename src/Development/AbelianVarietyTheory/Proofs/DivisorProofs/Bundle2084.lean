import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

namespace GlobalTheory.TwistChr

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hecke_eq_of_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) (χ : HChar E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ → r σ = (χ.val v)⁻¹)
    (x : Ideles E) (σ : G E Ω) (hx : art x = toAb E Ω σ) : χ.1 x = r σ := by
  have hc := continuous_of_isOpen_ker' r hr
  have h : (liftAb r hc).comp art * χ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ (((continuous_liftAb r hc).comp ha.quot.continuous).mul χ.2.1.inv) (fun k => ?_) S
      fun v hv => ?_
    · have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, χ.2.2, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one, inv_one, one_mul]
    · refine GlobalTheory.FrobDense.eq_one_of_unif (((liftAb r hc).comp art * χ.1⁻¹).comp (localIdele E v)) fun y hy => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨τ, hτ, e⟩ := (ha.frob v A hA _).mp ⟨y, hy, rfl⟩
      have h1 : χ.1 (localIdele E v y) = χ.val v := χ.val_eq (hu v hv) y hy
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← e, liftAb_toAb, map_inv,
        hf v hv A hA τ hτ, inv_inv, h1, mul_inv_cancel]
  have h2 := DFunLike.congr_fun h x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hx, liftAb_toAb, MonoidHom.one_apply, mul_inv_eq_one] at h2
  exact h2.symm

theorem chrEq_charOf {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] [IsAlgClosure D.host.E Ω] {a : Recip D Ω} (ha : a.Good)
    {R : Type} [CommRing R] (f : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (hψ : IsOpen (ψ.ker : Set (G D.host.E Ω))) {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ σ, ψ σ ^ n = 1) (χ : HChar D.host.E) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) A (normV v) σ →
      f (ψ σ : Rˣ) = (((χ.val v)⁻¹ : ℂˣ) : ℂ)) : ChrEq (charOf a f ψ) χ := by
  have key : ∀ x, ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := fun x => by
    obtain ⟨σ, hσ⟩ := a.exists_sym x
    rw [charOf_eq a f hψ hσ hn (hp σ), hecke_eq_of_frob ha.artin ((Units.map f.toMonoidHom).comp ψ)
      (Subgroup.isOpen_mono (H₁ := ψ.ker) (fun g hg => by
        rw [MonoidHom.mem_ker] at hg ⊢
        rw [MonoidHom.comp_apply, hg, map_one]) hψ) χ S hu (fun v hv A hA τ hτ => Units.ext (hf v hv A hA τ hτ)) _ σ hσ]
    rfl
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_induced_rng.2 ?_
    exact (Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ ha.cont))).congr fun x => (key x).symm
  · refine Circle.ext ?_
    rw [key, show Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k from Units.ext (ha.rat k), χ.2.2]
    rfl
  · rw [key, show Units.map a.κ.toMonoidHom x = localIdele D.host.E P (atFin P k) from Units.ext (by
      change a.κ (x : AE D) = _
      rw [hx, ha.loc P e he k])]
    rfl

theorem chrEq_mul {D : D7} {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx]
    rfl

theorem finite_placesOver (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l ≠ 0) : (Formalism.BasicNotions.placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}

theorem chrEq_tw (h : RecTies p) (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (hψ : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hA : Adapted p w ρ) :
    ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) := by
  classical
  obtain ⟨-, -, hopen, -, hzk, -, -⟩ := hψ
  obtain ⟨-, e, he, he'⟩ := hA
  have hl : D.ntw.l (ex.nch.twI w) ≠ 0 := (D.ntw.lPrime _).out.ne_zero
  have hz : D.ntw.zk (ex.nch.twI w) (ex.nch.k' w) ^ (D.ntw.l (ex.nch.twI w) ^ ex.nch.k' w) = 1 :=
    Units.ext (by simpa using (D.ntw.zk_prim (ex.nch.twI w) (ex.nch.k' w)).pow_eq_one)
  have hfin := finite_placesOver D.host.E (l := D.what₂.places.resChar w) (ex.nch.twI_l w ▸ hl)
  refine chrEq_charOf hρ.rc _ _ hopen (pow_ne_zero (ex.nch.k' w) hl) (fun σ => ?_) _ (ex.nch.Q w ∪ hfin.toFinset)
    (fun v hv => ((p.Tp.psi_is w hw).ram v).2 fun hQ => hv (Finset.mem_union_left _ hQ)) fun v hv A hA σ hσ => ?_
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · obtain ⟨y, hy, hy'⟩ := h.psi_read w hw v (fun hQ => hv (Finset.mem_union_left _ hQ))
      (fun hQ => hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hQ))) A σ hA hσ
    rw [← he', ← hy', he, hy]

theorem xi_eq (hw : D.what₂.muAt w ≠ D.what₂.mu0) {ρ : Setup D.ntw} (hP : RealPin p.R p.cG ρ) (j : Fin D.R.m) (b : Bool)
    {c : (AE D)ˣ →* Circle} (hc : ChrEq c (p.Tp.psi w)) :
    p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j b).de.chi * c := by
  have h1 := p.charW.base.lev.xi (p.R.mu (D.plEq w))
  have h2 : p.R.toRealDat.toLevCh.xiH (p.R.mu (D.plEq w)) = p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w := by
    rw [← p.tupAt w, p.tupXi _ (Or.inr ⟨w, rfl⟩), (D.what₂.muAt_or w).resolve_left hw, p.Tp.xi_tw, ex.nch.twI_l]
  exact GlobalTheory.ChrEqUnique.idc_unique D _ _ _ h1 (h2 ▸ chrEq_mul (hP.delta _ j b) hc)

end Point

theorem twChr_of_twAdm : GlobalTheory.Published.GlobalArtinReciprocity → TwAdm → TwChr := fun _ h =>
  Closed.imp h fun _ _ _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p r hm w hw j _ hρ hA =>
    have hw' := (p.tw_iff w).1 hw
    have h1 := chrEq_tw hm.2.2 hw' (H x hx h0 i p r hm w hw j).1 hρ hA
    ⟨h1, xi_eq hw' hA.1 j _ h1⟩⟩

end GlobalTheory.TwistChr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBounds
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BinomRatio
open Finset

theorem fact_mul_choose_eq_prod (T a n : ℕ) :
    ((n.factorial : ℕ) : ℝ) * (((T + a + n).choose n : ℕ) : ℝ)
      = ∏ i ∈ range n, ((T : ℝ) + a + 1 + i) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose (T + a) n
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h2 : ((∏ i ∈ range n, (T + a + 1 + i) : ℕ) : ℝ) = ((n.factorial * (T + a + n).choose n : ℕ) : ℝ) := by
    rw [h]
  push_cast at h2
  rw [← h2]

theorem prod_upper (T a n : ℕ) :
    ∏ i ∈ range n, ((T : ℝ) + a + 1 + i)
      ≤ (1 + (a : ℝ) / (T + 1)) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hc : (1 + (a : ℝ) / (T + 1)) ^ n = ∏ _i ∈ range n, (1 + (a : ℝ) / (T + 1)) := by simp
  rw [hc, ← prod_mul_distrib]
  apply prod_le_prod
  · intro i _; positivity
  · intro i _
    have hT : (0 : ℝ) < T + 1 := by positivity
    have hi : (0 : ℝ) ≤ i := by positivity
    have ha : (0 : ℝ) ≤ a := by positivity
    have e : (1 + (a : ℝ) / (T + 1)) * ((T : ℝ) + 0 + 1 + i) = (T + 1 + i) + a + a * i / (T + 1) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (a : ℝ) * i / (T + 1) := by positivity
    linarith

theorem prod_lower (T c n : ℕ) (hc : (c : ℝ) ≤ T) (hT : 0 < T) :
    (1 - (c : ℝ) / T) ^ n * ∏ i ∈ range n, ((T : ℝ) + c + 1 + i)
      ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hcp : (1 - (c : ℝ) / T) ^ n = ∏ _i ∈ range n, (1 - (c : ℝ) / T) := by simp
  rw [hcp, ← prod_mul_distrib]
  apply prod_le_prod
  · intro i _
    have : (0 : ℝ) ≤ 1 - c / T := by rw [sub_nonneg, div_le_one hT']; exact hc
    positivity
  · intro i _
    have hi : (0 : ℝ) ≤ i := by positivity
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have e : (1 - (c : ℝ) / T) * ((T : ℝ) + c + 1 + i) = (T + 1 + i) - (c * c + c * (1 + i)) / T := by
      field_simp; ring
    rw [e]
    have : 0 ≤ ((c : ℝ) * c + c * (1 + i)) / T := by positivity
    linarith

end GlobalTheory.BinomRatio

namespace GlobalTheory.BinomRatio
open Finset

theorem first_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n := by
  have e1 : T + 3 * n + 10 = T + (2 * n + 10) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hA := fact_mul_choose_eq_prod T (2 * n + 10) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hU := prod_upper T (2 * n + 10) n
  set x : ℝ := ((2 * n + 10 : ℕ) : ℝ) / (T + 1) with hx
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hnx : (n : ℝ) * x ≤ 0.65 := by
    rw [hx, mul_div_assoc', div_le_iff₀ hT1]
    push_cast
    nlinarith
  have hpow : (1 + x) ^ n ≤ 2 := by
    calc (1 + x) ^ n ≤ (Real.exp x) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp x; linarith
      _ = Real.exp (n * x) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have := Real.log_two_gt_d9; linarith
      _ = 2 := Real.exp_log (by norm_num)
  have hP : 0 ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
    apply prod_nonneg; intro i _; positivity
  have key : ((n.factorial : ℕ) : ℝ) * (((T + (2 * n + 10) + n).choose n : ℕ) : ℝ)
      ≤ ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hA]
    calc ∏ i ∈ range n, ((T : ℝ) + ((2 * n + 10 : ℕ) : ℝ) + 1 + i)
        ≤ (1 + x) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := hU
      _ ≤ 2 * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := mul_le_mul_of_nonneg_right hpow hP
      _ = ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
          push_cast at hB ⊢
          rw [← hB]; ring
  have := le_of_mul_le_mul_left key hf
  exact_mod_cast this

theorem second_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) := by
  have e1 : T + 2 * n + 6 = T + (n + 6) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hT0 : 0 < T := by nlinarith
  have hTR0 : (0 : ℝ) < T := by exact_mod_cast hT0
  have hc : (((n + 6 : ℕ)) : ℝ) ≤ T := by push_cast; nlinarith
  have hA := fact_mul_choose_eq_prod T (n + 6) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hL := prod_lower T (n + 6) n hc hT0
  have hbern : 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) ≤ (1 + -((((n + 6 : ℕ)) : ℝ)) / T) ^ n := by
    apply one_add_mul_le_pow
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hTR0]
    linarith
  have hC : (0 : ℝ) ≤ (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by positivity
  have step : (1 - (n : ℝ) * (n + 6) / T) * (((T + (n + 6) + n).choose n : ℕ) : ℝ)
      ≤ (1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hC
    have h1 : (1 : ℝ) - (n : ℝ) * (n + 6) / T = 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) := by
      push_cast; ring
    have h2 : (1 : ℝ) - (((n + 6 : ℕ)) : ℝ) / T = 1 + -((((n + 6 : ℕ)) : ℝ)) / T := by ring
    rw [h1, h2]; exact hbern
  have key : ((n.factorial : ℕ) : ℝ) * ((1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ))
      ≤ ((n.factorial : ℕ) : ℝ) * (((T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hB, mul_left_comm, hA]
    simpa only [Nat.cast_zero] using hL
  have := le_of_mul_le_mul_left key hf
  linarith

theorem two_binom_ratios : ∀ T n : ℕ, 2 ≤ n → 11 * n ^ 2 ≤ T →
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) :=
  fun T n hn hT => ⟨first_ratio T n hn hT, second_ratio T n hn hT⟩

end GlobalTheory.BinomRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFiniteOfComponents
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

namespace GlobalTheory.CompFin

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in

theorem castFrame_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ' r) :
    castFrame h (castFrame h.symm x) = x := rfl

theorem castFrame_mem_GG (X : Data E r) {Ψ : Finset (E →+* ℂ)} (h : X.Ψ = Ψ) (x : Frame X.Ψ r) :
    castFrame h x ∈ GG Ψ X.Gm X.p0 ↔ x ∈ X.dom := by
  subst h
  rfl

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem castFrame_mem_dom (c : C) (x : Frame (M.comp c).Ψ r) :
    castFrame (M.comp_Ψ c) x ∈ M.dom ↔ x ∈ (M.comp c).dom := by
  have := castFrame_mem_GG (M.comp c).toData (M.comp_Ψ c) x
  rw [M.comp_Gm c, M.comp_basePoint c] at this
  exact this

def toComp (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] ((M.comp c).dom → ℂ) where
  toFun v x := v c ⟨castFrame (M.comp_Ψ c) x.1, (castFrame_mem_dom M c x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cusp_le_comap (ka : Wt M.Ψ r) (c : C) :
    M.cusp ka ≤ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) ''
      (M.comp c).SS (castWt (M.comp_Ψ c) ka))).comap (toComp M c) := by
  unfold TwoLevels.cusp
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  exact Submodule.subset_span ⟨_, hF c, rfl⟩

theorem toComp_inj (v w : C → M.dom → ℂ) (h : ∀ c, toComp M c v = toComp M c w) : v = w := by
  funext c y
  have hy : castFrame (M.comp_Ψ c).symm y.1 ∈ (M.comp c).dom :=
    (castFrame_mem_dom M c _).1 (by rw [castFrame_castFrame]; exact y.2)
  have := congrFun (h c) ⟨_, hy⟩
  exact this

end

end GlobalTheory.CompFin

open GlobalTheory.CompFin in

theorem GlobalTheory.cusp_finite_of_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r), (∀ c : C, FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka)))) → Module.Finite ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ M ka hfin
  let S : (c : C) → Submodule ℂ ((M.comp c).dom → ℂ) := fun c => Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ =>
    fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka))
  have : ∀ c, Module.Finite ℂ (S c) := hfin
  let Φ : M.cusp ka →ₗ[ℂ] (∀ c, S c) := LinearMap.pi fun c =>
    ((toComp M c).domRestrict (M.cusp ka)).codRestrict (S c) fun v => cusp_le_comap M ka c v.2
  have hΦ : Function.Injective Φ := by
    intro v w hvw
    apply Subtype.ext
    apply toComp_inj M
    intro c
    have := congrArg Subtype.val (congrFun hvw c)
    exact this
  exact Module.Finite.of_injective Φ hΦ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterEqOneSplitInert
section
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertSuppChar

theorem eq_one_at_inert {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (μ : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* Circle)
    (hμ : ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → μ k = 1)
    {q : ℕ} (hq : q.Prime) (hi : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) :
    μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 := by
  obtain ⟨g, hg⟩ := GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG y rfl
  rw [← GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hg]
  obtain ⟨l, hl, e⟩ := GlobalTheory.T.exists_prod_localComponents_eq_primePart V hG q hq g
  rw [← e, map_list_prod, map_list_prod, List.map_map]
  refine List.prod_eq_one (M := Circle) fun z hz => ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hz
  obtain ⟨v, ε, hε, hqv, hs⟩ := hl h hh
  have hn : GlobalTheory.WeilParts.NonSplitAt D v ε := (GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq v ε hε hqv).1 hi
  refine GlobalTheory.InertChar.char_eq_one_of_nonSplit D V _
    (GlobalTheory.NormRatio.SphCoset.isSelfDualC_of_gram_one hG (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D V.rank)) v ε hn
    (μ.comp (GlobalTheory.BotClassDict.finStd V hG)) (fun k hk hst => ?_) h hs
  obtain ⟨a1, a2⟩ := GlobalTheory.T.nonSplitSupported_finitePart_integral_inert V hG v ε hn k hk hst
  exact hμ _ a1 a2

theorem char_eq_one : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D), V.gram = 1 → ∀ (ν : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* ℂˣ),
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
    Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  ∀ x, ν x = 1 := by
  intro D V hG ν hs hi x
  refine GlobalTheory.T.eq_one_of_forall_circle_char_eq_one ν x fun μ hμ => ?_
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun q => ¬ Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x, map_mul,
    hμ _ (hs _ (GlobalTheory.NormSum.VacInt.suppSplit_part D x)), one_mul]
  have hy := GlobalTheory.NormSum.VacInt.suppInert_part D x
  generalize GlobalTheory.NormSum.VacInt.part D (fun q => ¬¬Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x = y at hy ⊢
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite y hy
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun p => p ∈ s) y, map_mul,
    hμ _ (hi _ (GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes _ _ hy) hs2), mul_one]
  have hloc : ∀ q, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 :=
    fun q hq hqi => eq_one_at_inert V hG μ (fun k a1 a2 => hμ _ (hi k a1 a2)) hq hqi y
  clear hs2
  induction s using Finset.induction_on with
  | empty => rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).1, map_one]
  | insert q s hq ih =>
    rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).2 q s hq, map_mul, hloc q (hs1 q (Finset.mem_insert_self q s)).1
      (hs1 q (Finset.mem_insert_self q s)).2, one_mul]
    exact ih fun p hp => hs1 p (Finset.mem_insert_of_mem hp)

end GlobalTheory.InertSuppChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelEvaluation
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem vanish_of_block_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Φ ∈ M.So B.ψ B.τ₁, ∀ (g : UA σ X.J) (h : UA σ W.J) (ξ : Fin n × Fin d → F), (∃ i, ∀ j ∈ blk i, ξ j = 0) →
      e (om (g, h) Φ) (fun j => algebraMap F (AF F) (ξ j)) = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y hfr M₁ blk e hG hco hev Φ hΦ g h ξ hξ
  obtain ⟨i, hi⟩ := hξ
  have htor := GlobalTheory.T.unitary_torus_element_exists F E σ B n X r s hP.base hP.herm q x y hfr
  have hblk := GlobalTheory.T.frame_torus_lattice_action F E σ B n d X W q x y M₁ blk hG hco htor i
  have hW := IsUWeilPair.isUSplitting hP.weil
  set ξ' : Fin n × Fin d → AF F := fun j => algebraMap F (AF F) (ξ j) with hξ'
  let Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => e (om (g, h) Ψ) ξ'
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hxi : x i ≠ 0 := by
    intro h0
    have := hfr.2.2 i i
    simp [h0, form] at this
  have hc := GlobalTheory.T.unitary_inverse_infinite_nonzero F E σ B n X.J g (x i) hxi
  refine GlobalTheory.T.pair_functional_nonvanishing hKP F E σ B n d X W M χX χW om r s r' s' hP Λ (mat g⁻¹ *ᵥ incV F (x i)) hc ?_ Φ hΦ
  intro z _ _ Ψ hΨ
  show e (om (g, h) (M.co.rho B.ψ _ Ψ)) ξ' = e (om (g, h) Ψ) ξ'
  rw [hW.impl (g, h) _ Ψ hΨ]
  have hgg : mat g * mat g⁻¹ = 1 := by simp [mat]
  have hgen : ∀ (A : Matrix (Fin n) (Fin n) (AE F E)) (Bm : Matrix (Fin d) (Fin d) (AE F E))
      (u : Fin n → AE F E) (w : Fin d → AE F E), A * Matrix.vecMulVec u w * Bmᵀ = Matrix.vecMulVec (A *ᵥ u) (Bm *ᵥ w) := by
    intro A Bm u w
    ext k l
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hact : actAB (cA σ) (g, h) (Matrix.vecMulVec (mat g⁻¹ *ᵥ incV F (x i)) z) =
      Matrix.vecMulVec (incV F (x i)) (mat h *ᵥ z) := by
    change mat g * _ * (mat h)ᵀ = _
    rw [hgen, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  rw [hact]
  obtain ⟨z', hz', hze⟩ := hblk (mat h *ᵥ z)
  have hΨ2 : om (g, h) Ψ ∈ schA F _ := hW.pres _ _ hΨ
  have hheis := hev.Heisenberg₂ (Matrix.vecMulVec (incV F (x i)) (mat h *ᵥ z)) _ hΨ2
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM, Matrix.map_one]
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by
    simp [incM, Matrix.map_one]
  rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at hheis
  rw [hheis]
  have hdot : ξ' ⬝ᵥ z' = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ blk i
    · simp [hξ', hi j hj]
    · simp [hz' j hj]
  simp only [Darboux.rho, hze, schr, hdot, zero_dotProduct, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThKTorus
end
end

