import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.RowLat
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
import Formalism.LocalToGlobal.Columns.Bundle0014
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfTie
section
noncomputable section

namespace GlobalTheory.ConjSpan

section General

open Formalism.IndefR.Bridge Formalism.L2.DIV

theorem span_eq_top {G Γ W W' K V₀ H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Field K] [NumberField K] [StarRing K] [AddCommGroup V₀] [Module K V₀]
    [AddCommGroup H] [Module ℂ H] {ι : Γ →* G} {S : CSD K} {τ σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {ρ' : Γ →* Module.End ℂ W'} {J : Subgroup G} {χ χ' : J →* ℂˣ} (P : ClassPres ι S τ ρ J χ)
    (c₀ : V₀ →ₛₗ[τ] W) (c₁ : V₀ →ₛₗ[σ] W') (e : S.V ≃ₗ[K] V₀) (he : ∀ x, P.coef x = c₀ (e x))
    (hspan : Submodule.span ℂ (Set.range c₁) = ⊤)
    (hact : ∀ γ v, ∃ v', c₀ v' = ρ γ (c₀ v) ∧ c₁ v' = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ a : K, τ a = (χ k : ℂ) ∧ σ a = (χ' k : ℂ))
    (E : H →ₗ[ℂ] (G → W')) (hE : Function.Injective E) (hr : LinearMap.range E = AdForms ι ρ' J χ')
    (j : S.Forms → H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ E (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  classical
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [PresBasic.coef_injective P h]
  have hval : ∀ (x : S.Forms) c, E (j x) (P.y c) = c₁ (e ((x : S.Cl → S.V) c)) := by
    intro x c
    obtain ⟨v, h1, h2⟩ := hj x (P.y c)
    rw [ClassPres.extL_apply, PresBasic.ext_y, he] at h1
    rw [h2, hinj h1]
  have hρ : ∀ c (g : S.Gam c) (x : S.V), c₁ (e (S.ρ c g x)) =
      (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) (c₁ (e x)) := by
    intro c g x
    obtain ⟨a, ha, ha'⟩ := hχ (stabK ι (P.stabI c g))
    obtain ⟨v', h1, h2⟩ := hact (P.stabI c g : Γ) (e x)
    have h3 : e (S.ρ c g x) = a • v' := by
      apply hinj
      rw [← he, P.coef_act, map_smulₛₗ, ha, h1, he]
    rw [h3, map_smulₛₗ, ha', h2]
  have hmem : ∀ w, E w ∈ AdForms ι ρ' J χ' := fun w => hr ▸ LinearMap.mem_range_self E w
  have hone : ∀ c (u : W'), ∃ w ∈ Submodule.span ℂ (Set.range j), ∀ c', E w (P.y c') =
      (Pi.single c (∑ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) u) : S.Cl → W') c' := by
    intro c u
    have hu : u ∈ Submodule.span ℂ (Set.range c₁) := hspan ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      obtain ⟨x, rfl⟩ := e.surjective v
      refine ⟨j (PresBasic.avgForm S c x), Submodule.subset_span ⟨_, rfl⟩, fun c' => ?_⟩
      rw [hval]
      by_cases h : c' = c
      · subst h
        simp only [PresBasic.avgForm, Pi.single_eq_same, map_sum, hρ]
      · simp [PresBasic.avgForm, Pi.single_eq_of_ne h]
    | zero => exact ⟨0, Submodule.zero_mem _, fun c' => by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨w, hw, h⟩ := h
      obtain ⟨w', hw', h'⟩ := h'
      refine ⟨w + w', Submodule.add_mem _ hw hw', fun c' => ?_⟩
      simp only [map_add, Pi.add_apply, h, h', smul_add, Finset.sum_add_distrib, Pi.single_add]
    | smul a u _ h =>
      obtain ⟨w, hw, h⟩ := h
      refine ⟨a • w, Submodule.smul_mem _ _ hw, fun c' => ?_⟩
      simp only [map_smul, Pi.smul_apply, h, smul_comm _ a, ← Finset.smul_sum, Pi.single_smul]
  rw [eq_top_iff]
  intro w _
  choose f hf hf' using fun c => hone c ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c))
  have key : w = ∑ c, f c := by
    apply hE
    funext g
    obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
    rw [hmem w γ _ k, hmem _ γ _ k]
    congr 2
    rw [map_sum, Finset.sum_apply]
    simp only [hf']
    rw [Finset.sum_eq_single c (fun c' _ hc => Pi.single_eq_of_ne (Ne.symm hc) _) (by simp), Pi.single_eq_same]
    have hg : ∀ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ)
        ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c)) = (Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c) := by
      intro g
      have h1 := hmem w (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
      rw [stabK_spec] at h1
      rw [map_smul, smul_comm, ← h1]
    simp only [hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast Fintype.card_ne_zero
  rw [key]
  exact Submodule.sum_mem _ fun c _ => hf c

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem span_eq_top_of_tie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ χ' : J →* ℂˣ} (P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c₀ : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : Bridge.CoefTie V C P lam c₀ pair nab del) (hM : Bridge.CoefMapTie V C c₀ rho)
    {σ : D.what₂.LL →+* ℂ} (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W)
    (hact : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, c₁ (rho γE v) = c.ρ (γ : GA D V) (c₁ v))
    (hspan : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤)
    (hχ : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjVal σ ((χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ))
    (H : HMod (Bridge.Gf V → c.W)) {ip} (hH : H.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ') ip)
    (j : S.Forms → H.H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨e, -, he, -⟩ := hP
  have hspan' : Submodule.span ℂ (Set.range c₁) = ⊤ :=
    eq_top_iff.2 (hspan.ge.trans (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)))
  refine span_eq_top (ρ' := c.coef.ρ) P c₀ c₁ e he hspan' (fun γ v => ?_) hχ H.e hH.1 hH.2.1 j hj
  obtain ⟨γE, h⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  exact ⟨_, hM.1 γ γE h v, hact γ γE h v⟩

set_option maxHeartbeats 1600000 in

theorem span_conjForms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → Submodule.span ℂ (Set.range j) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC
  obtain ⟨χ', hχ, hH⟩ := hC.model
  have h1 := hT.coefL i A.μ0
  have h2 := hT.mapL i
  refine span_eq_top_of_tie (V := Vc D i) (R.B.L i A.μ0).pres h1 h2 c c₁ hC.act hC.span hχ H hH j fun x h => ?_
  have h0 := congrFun (hjV i A.μ0 x) h
  exact (hC.base x h).imp fun v hv => ⟨h0.symm.trans hv.1, hv.2⟩

end GlobalTheory.ConjSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SplitFullyNorm

theorem exists_prime_absNorm_eq_of_splitsFully (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (W : HeightOneSpectrum (𝓞 E)) (h : SplitsFully E (W.under (𝓞 F))) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  classical

  set P : Ideal ℤ := W.asIdeal.under ℤ with hPdef
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot W.ne_bot
  haveI hPprime : P.IsPrime := Ideal.IsPrime.under ℤ W.asIdeal
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0

  have hunder : (W.under (𝓞 F)).asIdeal.under ℤ = P := by
    change (W.asIdeal.under (𝓞 F)).under ℤ = W.asIdeal.under ℤ
    exact Ideal.under_under _
  have hcard : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
    have h' := h
    unfold SplitsFully at h'
    rwa [hunder] at h'

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum

  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q
    haveI : q.1.IsPrime := q.2.1
    have hpos := Nat.mul_pos (Ideal.ramificationIdx_pos q.1 ℤ) (Ideal.inertiaDeg_pos q.1 ℤ)
    by_contra hne
    have hlt : ∑ _r : P.primesOver (𝓞 E), (1 : ℕ) <
        ∑ r : P.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
      apply Finset.sum_lt_sum
      · intro r _
        haveI : r.1.IsPrime := r.2.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos r.1 ℤ) (Ideal.inertiaDeg_pos r.1 ℤ)
      · exact ⟨q, Finset.mem_univ _, by omega⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq, hcard] at hlt
    exact lt_irrefl _ hlt
  have hWmem : W.asIdeal ∈ P.primesOver (𝓞 E) := ⟨W.isPrime, ⟨rfl⟩⟩
  have hw := hone ⟨W.asIdeal, hWmem⟩
  have he : W.asIdeal.ramificationIdx ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hw
  have hf : W.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left hw

  set n : ℕ := (Submodule.IsPrincipal.generator P).natAbs with hn
  have hspan : Ideal.span {((n : ℕ) : ℤ)} = P := by
    rw [hn, Int.span_natAbs, Ideal.span_singleton_generator]
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply hP0
    rw [← hspan, h0, Ideal.span_singleton_eq_bot]
  have hnprime : n.Prime := by
    rw [Nat.prime_iff_prime_int, ← Ideal.span_singleton_prime hn0, hspan]
    exact hPprime
  haveI : W.asIdeal.LiesOver (Ideal.span {((n : ℕ) : ℤ)}) := ⟨by rw [hspan]⟩
  refine ⟨n, hnprime, ?_, ?_⟩
  ·
    rw [← Ideal.pow_inertiaDeg n W.asIdeal, hf, pow_one]
  ·
    intro hmem
    have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ W.asIdeal ^ 2 := by
      rw [← hspan, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    have hdvd : W.asIdeal ^ 2 ∣ P.map (algebraMap ℤ (𝓞 E)) := Ideal.dvd_iff_le.mpr hle
    have hfin : FiniteMultiplicity W.asIdeal (P.map (algebraMap ℤ (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact W.isPrime.ne_top) hmap0
    have h2 := hfin.le_multiplicity_of_pow_dvd hdvd
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P W.asIdeal hmap0, he] at h2
    omega

end GlobalTheory.SplitFullyNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem grp_similitude_herm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : grp G β), ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))ᴴ * herm G v β *
      (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) = (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β := by
  intro p _ G v β y
  obtain ⟨⟨u, s⟩, hy, _⟩ := y
  change (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β at hy
  have hV : ((toV G v β ⟨(u, s), hy, ‹_›⟩ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (u : G.C) := rfl
  rw [hV]
  change (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
    ((s : ℚ) : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C))
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hu : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u =
      algebraMap ℚ G.C (s : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (u * β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (u : G.C) * β * (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u)
        = ((u : G.C) * β * sh G (u : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) * u := by
          simp only [mul_assoc]
      _ = (s : ℚ) • ((β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
          rw [hy, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (s : ℚ) • ((u : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (u : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v (u : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((s : ℚ) : ℚ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem natCast_notMem_of_not_dvd [StarRing K] (w : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ m) : (m : 𝓞 K) ∉ w.asIdeal := by
  intro h
  apply hm
  have h1 : ((m : ℕ) : 𝓞 K ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  unfold Formalism.EigenvalueLevelCeiling.plc
  exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) m).1 h1

theorem factor_mem (w : HeightOneSpectrum (𝓞 K)) (p e n : ℕ) (ν : Fin n → ℕ)
    (hpw : ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 K) ∉ w.asIdeal) (hI : Formalism.CohomologicalDescent.LA.InclZ n n le_rfl ν p e) :
    ∀ f ∈ (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν).map (toK K (Fin n × Fin n)),
      ((p : K) ^ e) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
        ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K (Fin n × Fin n))) := by
  obtain ⟨m, hm, hmx⟩ := hI
  have hm0 : (m : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hm (dvd_zero p)
  have hval : w.valuation K ((m : K)⁻¹) ≤ 1 := by
    have h1 : w.valuation K (algebraMap (𝓞 K) K (m : 𝓞 K)) = 1 :=
      (w.valuation_eq_one_iff_notMem).2 (hpw m hm)
    rw [map_natCast] at h1
    rw [map_inv₀, h1, inv_one]
  rintro _ ⟨g, hg, rfl⟩
  rw [GlobalTheory.StdDual.dualWeyl_eq, ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))] at hg
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨b, hb, rfl⟩ := hq
    have hbD : b ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.subset_span hb
    have h1 := GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) le_rfl ν _ (hmx b hbD)
    have h2 := GlobalTheory.JetOpWeylLat.smul_mem_localizationAt_of_valuation w hval (Submodule.mem_map_of_mem (f := toK K (Fin n × Fin n)) h1)
    convert h2 using 1
    rw [GlobalTheory.JetOpWeylLat.toK_map_int, GlobalTheory.JetOpWeylLat.toK_map_int, map_zsmul, ← Int.cast_smul_eq_zsmul K,
      smul_smul]
    congr 1
    push_cast
    field_simp
  | zero => simpa using zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add, smul_add]
    exact add_mem ha hb
  | smul a g _ hg =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ a hg

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem tensor_mem (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (c : K)
    (e : ι → ℕ)
    (h : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      (c ^ e τ) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)))) :
    ∀ z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      (c ^ ∑ τ, e τ) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  classical
  have key : ∀ y ∈ nabStd K lam, (c ^ ∑ τ, e τ) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro y hy
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hy
    induction hy using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨F, hF, rfl⟩ := hP
      choose t ht hFt using fun τ => (lc_mem_locP w _ _).1 (h τ (F τ) (hF τ))
      have hnot : (∏ τ, t τ) ∉ w.asIdeal :=
        Submonoid.prod_mem w.asIdeal.primeCompl (t := Finset.univ) (f := t) (fun τ _ => ht τ)
      refine (lc_mem_locP w _ _).2 ⟨∏ τ, t τ, hnot, ?_⟩
      have hFt' : ∀ τ, (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ ∈
          (delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)) := fun τ => by
        have e1 : t τ • c ^ e τ • F τ = (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ :=
          (algebraMap_smul K (t τ) _).symm.trans (smul_smul _ _ _)
        convert hFt τ using 1
        exact e1.symm
      have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) ∈ delStd K lam :=
        Submodule.subset_span ⟨_, hFt', rfl⟩
      have e2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) =
          ((algebraMap (𝓞 K) K (∏ τ, t τ)) * c ^ ∑ τ, e τ) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ) := by
        simp only [map_smul, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod, map_mul,
          Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.rename_C]
        congr 2
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
      rw [e2] at hmem
      convert hmem using 1
      exact (algebraMap_smul K (∏ τ, t τ) _).symm.trans (smul_smul _ _ _)
    | zero => simpa using zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul a y _ hy =>
      have e3 : (c ^ ∑ τ, e τ) • a • y = a • (c ^ ∑ τ, e τ) • y := smul_comm _ _ _
      convert Submodule.smul_mem _ a hy using 1
      exact e3
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (lc_mem_locP w _ _).1 hz
  obtain ⟨t, ht, htz⟩ := (lc_mem_locP w _ _).1 (key _ hsz)
  refine (lc_mem_locP w _ _).2 ⟨t * s, lc_mul_notMem w ht hs, ?_⟩
  convert htz using 1
  exact (mul_smul t s _).trans (congrArg (t • ·) (smul_comm s _ z))

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

theorem exZ_sum_smul_mem_locP_delAtr :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ)
      (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L,
        (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  intro E K _ _ _ _ _ ι _ n emb lam L hL w x hx
  have hM : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ L)) := fun τ =>
    du_dualFr_lattice basisAtEx _ (tauLatLattice E K ι n emb τ L hL)
  choose B hB using fun τ => basisAtEx K n _ (hM τ) w
  have hx1 : (x : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ L)) :=
    lc_le_locP w _ hx
  rw [(nabDelLoc K ι n lam _ hM w B hB).1] at hx1
  obtain ⟨z, hz, hzx⟩ := hx1
  have hfac : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      ((Formalism.EigenvalueLevelCeiling.plc w : K) ^ Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w)) • f ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n))) := fun τ =>
    factor_mem w (Formalism.EigenvalueLevelCeiling.plc w) _ n (lam τ).natW (fun m hm => natCast_notMem_of_not_dvd w hm)
      (Formalism.CohomologicalDescent.LA.exact_z_specialization n n le_rfl _ (natW_antitone _) _ (Formalism.EigenvalueLevelCeiling.plc_prime w))
  have hz' := tensor_mem w lam (Formalism.EigenvalueLevelCeiling.plc w : K) _ hfac z hz
  refine (GlobalTheory.LvT.Built.ValLat.mem_localization_delAtr emb lam w hL B hB _).2 ⟨_, hz', ?_⟩
  have e1 : (actP lam B) z = (x : Pol K ι n) := hzx
  rw [map_smul, e1]
  refine (algebraMap_smul K (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^
    (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) (x : Pol K ι n)).symm.trans ?_
  simp only [map_pow, map_natCast]

end GlobalTheory.OntoExponentsLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZero
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecNe

theorem thPVec_ne_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hr : T.rank ≤ S.rank) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) : f ≠ 0 := by
  obtain ⟨hv, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have h0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.2.norm
    have := h2 p hp
    simp [nrm2] at this
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinf := ho.conj.infPart_eq
  rw [hall Tm hTm]
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.AdjDatumNe.exists_datum_ne_zero D S T βS βT Pg Q _ ξ e hr he
    (fun PP h => Finset.mem_union_left _ h) fun PP h => Finset.mem_union_right _ h
  refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D ψ S T ΛS ΛT _ f₀ _ Tm hv.1 hS hT ho.conj.idem
    (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h0
    (GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
      (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
    fun hz => h3 ?_
  have := congrFun hz x
  rwa [if_pos ⟨h1, h2⟩] at this

theorem thetaVector_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ i, VStd D i → R.vP i A.μ0 ≠ 0 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i _
  exact thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hC.thP.vP i A.μ0)

end GlobalTheory.AdTh.VecNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ → open Classical in IsToricSum φ s κ (condQ 𝔣 Q) χ (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ)) := by
  first | exact @GlobalTheory.ToricSumValue.toricSum_eq | exact GlobalTheory.ToricSumValue.toricSum_eq | (intros; apply GlobalTheory.ToricSumValue.toricSum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerNormInvariantStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_norm_invariant : ∀ {H : Type} [Group H] (θ : H →* H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, δ * θ z * δ⁻¹ ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) := by
  first | (exact @GlobalTheory.LKMid.TwCent.main) | (exact GlobalTheory.LKMid.TwCent.main) | (intros; apply GlobalTheory.LKMid.TwCent.main  <;> assumption)
end

