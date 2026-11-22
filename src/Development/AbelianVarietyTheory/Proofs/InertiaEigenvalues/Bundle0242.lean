import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActDEqOfEqOne
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.CutTrivIne

section Gen

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]

set_option synthInstance.maxHeartbeats 400000 in

theorem eq_zero_of_phi (k : ℕ) (x : KOG O k) (hx : Br.phi Bw k x = 0) : x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : Br.vecS Bw k v ∈ stdG (Br.Ow Bw) (Br.LLw Bw) k :=
    (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨u, hu⟩ := h1
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨fun j => Bw.eO.symm (u j), ?_⟩
  funext j
  apply (Br.toLLK Bw).injective
  have h2 := Br.toLLK_alg Bw (Bw.eO.symm (u j))
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.trans (congrFun hu j)

end Gen

theorem actD_eq_of_eq_one {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] {k : ℕ}
    (M : G →* Matrix (Fin k) (Fin k) LL) (L : Lattice (O := O) (matRep M)) (g : G) (hg : M g = 1)
    (x : (Fin k → LL) ⧸ L.T) : actD L g x = x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : matRep M g v = v := by
    show Matrix.toLin' (M g) v = v
    rw [hg, Matrix.toLin'_one]
    rfl
  show Submodule.Quotient.mk (matRep M g v) = _
  rw [h]

theorem chiRatO_one (D : D7) (i : D.nd.Loc) (γ : GE D.nd) : chiRatO D.nd i 1 γ = 1 := by
  simp [chiRatO, twistM]

set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ C, locFun i (chiRatO D.nd i 1) w hw f ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) → resIne i C w = ⊥ := by
  intro D i C w hw h
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, hx⟩ := h f hf
  rw [Submodule.mem_bot]
  funext γ
  obtain ⟨g, hg⟩ := (Br.ι_bijective (D.nbr i w hw)).2 ⟨γ.1, Ine_le_Dec _ γ.2⟩
  have hg' : ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) = γ.1 := congrArg Subtype.val hg
  have hmem : g ∈ Br.inert D.nbr i w hw := by
    show ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)
    rw [hg']
    exact γ.2
  have h1 : Br.loc D.nbr i w hw (chiRatO D.nd i 1) g = 1 := by
    show (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).mapMatrix
      ((D.nbr i w hw).eO.toRingHom.mapMatrix
        (chiRatO D.nd i 1 ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))) = 1
    rw [chiRatO_one, map_one, map_one]
  have h2 := hx g hmem
  rw [actD_eq_of_eq_one _ _ g h1, sub_self] at h2
  have h3 := eq_zero_of_phi (D.nbr i w hw) 1 _ h2
  rw [hg'] at h3
  exact h3

end GlobalTheory.CutTrivIne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalProdEqZeroHodgeTateCyclotomicFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_prod_eq_zero_hodgeTate_cyclotomicFrame : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → Polynomial.aeval (U g) (∏ u ∈ J, (Polynomial.X - Polynomial.C (chiC χ (-u) g))) = 0 := by
  first | exact @GlobalTheory.CycEigen.aeval_prod_eq_zero | exact GlobalTheory.CycEigen.aeval_prod_eq_zero | (intros; apply GlobalTheory.CycEigen.aeval_prod_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfInvPiModXiPowBoundedDenominatorStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_invPi_mod_xi_pow_bounded_denominator : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (k n M : ℕ), 1 ≤ M → k ≤ (l - 1) * n → ((l : ℕ) : Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} := by
  first | exact @GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator | exact GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator | (intros; apply GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesCharRepModPowLeOfDuality
section
open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift ReciprocityTheory.Gal

namespace GlobalTheory.Cyc.CocycleCount

theorem card_Z1_mul_card_H0 {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R G M) (h : ContAction rho) :
    Nat.card (Z1 rho) * Nat.card (H0 rho) = Nat.card M * Nat.card (H1 rho) := by
  have hker : LinearMap.ker (d0 rho) = H0 rho := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have hg := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at hg
      exact hg
    · intro h
      funext g
      rw [amitsur_d0_apply, Pi.zero_apply, h g, sub_self]
  have hM : Nat.card M = Nat.card (H0 rho) * Nat.card (B1 rho) := by
    rw [(LinearMap.ker (d0 rho)).card_eq_card_quotient_mul_card,
      Nat.card_congr (LinearMap.quotKerEquivRange (d0 rho)).toEquiv, hker]
    rfl
  have hZ : Nat.card (Z1 rho) = Nat.card (B1 rho) * Nat.card (H1 rho) := by
    rw [((B1 rho).comap (Z1 rho).subtype).card_eq_card_quotient_mul_card,
      Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles rho h)).toEquiv]
  rw [hZ, hM]
  ring

private theorem pow_sub_dvd_val_of_pow_mul_eq_zero {l : ℕ} (hl : 0 < l) (N r : ℕ) [NeZero (l ^ r)] (a : ZMod (l ^ r))
    (ha : (l : ZMod (l ^ r)) ^ N * a = 0) : l ^ (r - N) ∣ a.val := by
  rcases le_or_gt r N with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    exact one_dvd _
  · have h1 : ((l ^ N * a.val : ℕ) : ZMod (l ^ r)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact ha
    rw [CharP.cast_eq_zero_iff (ZMod (l ^ r)) (l ^ r)] at h1
    have h2 : l ^ r = l ^ N * l ^ (r - N) := by
      rw [← pow_add, Nat.add_sub_cancel' h.le]
    have h3 : l ^ N * l ^ (r - N) ∣ l ^ N * a.val := by
      rw [← h2]
      exact h1
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hl N) h3

private theorem card_le_pow_of_injective_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (N r : ℕ) {X : Type*} (f : X → ZMod (l ^ r))
    (hf : Function.Injective f) (hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0) :
    Nat.card X ≤ l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  let g : X → Fin (l ^ N) := fun x => ⟨(f x).val / l ^ (r - N), by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hl _), ← pow_add]
    calc (f x).val < l ^ r := ZMod.val_lt _
      _ ≤ l ^ (N + (r - N)) := Nat.pow_le_pow_right hl (by omega)⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    apply ZMod.val_injective
    have hx := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f x) (hann x)
    have hy := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f y) (hann y)
    have e : (f x).val / l ^ (r - N) = (f y).val / l ^ (r - N) := congrArg Fin.val hxy
    rw [← Nat.div_mul_cancel hx, ← Nat.div_mul_cancel hy, e]
  have hc := Nat.card_le_card_of_injective g hg
  simpa using hc

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G]

theorem card_invariants_twistedDual_charRep_le_pow (χ ψ : G →* ℤ_[l]ˣ) (N r : ℕ)
    (g₀ : G) (hg : ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ))) :
    Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ∧
    Nat.card (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ≤
      l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have key : ∀ (φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r))) (m : ZMod (l ^ r)), φ m = m * φ 1 := by
    intro φ m
    have h := LinearMap.map_smul (show Module.Dual (ZMod (l ^ r)) (ZMod (l ^ r)) from φ) m 1
    rw [smul_eq_mul, smul_eq_mul, mul_one] at h
    exact h
  let f : H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →
      ZMod (l ^ r) := fun x => x.1 1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply TDual.ext
    intro m
    rw [key x.1 m, key y.1 m]
    exact congrArg (m * ·) hxy
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1
    ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 hg.le)
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ)) := zpow_pos (by exact_mod_cast hl) _
  have hvn : ‖v‖ = 1 := by
    have hn := congrArg norm hv
    rw [norm_mul, PadicInt.norm_p_pow, hg] at hn
    exact mul_right_cancel₀ hpos.ne' (hn.trans (one_mul _).symm)
  have hvu : IsUnit (PadicInt.toZModPow r v) := (PadicInt.isUnit_iff.2 hvn).map _
  have hred : (redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1 =
      PadicInt.toZModPow r v * (l : ZMod (l ^ r)) ^ N := by
    have e := congrArg (PadicInt.toZModPow r) hv
    simp only [map_mul, map_pow, map_natCast, map_sub, map_one] at e
    rw [redChar_apply, redChar_apply, e]
  have hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0 := by
    intro x
    have h0 : ∀ g, twDual (redChar χ r) (charRep (redChar ψ r)) g x.1 = x.1 := by
      have hx := x.2
      exact hx
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) => φ 1) (h0 g₀)
    simp only [twDual_apply, charRep_apply, mul_one] at h1
    rw [key x.1] at h1
    have h2 : ((redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1) * f x = 0 := by
      show _ * x.1 1 = 0
      linear_combination h1
    rw [hred, mul_assoc] at h2
    exact hvu.mul_right_eq_zero.1 h2
  exact ⟨Finite.of_injective f hf, card_le_pow_of_injective_of_pow_mul_eq_zero N r f hf hann⟩

theorem card_cocycles_charRep_modPow_le_of_duality : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ ψ : G →* ℤ_[l]ˣ), (Continuous fun g => (ψ g : ℤ_[l])) → ∀ (N r d : ℕ) (g₀ : G), ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ)) → Nonempty (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar χ r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) → Function.Injective (ReciprocityTheory.Gal.cup20 (redChar χ r) (ReciprocityTheory.Gal.charRep (redChar ψ r)) (MonoidHom.id G)) → Nat.card (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ZMod (l ^ r)) ^ d → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ l ^ N * l ^ (r * (d + 1)) := by
  intro l _ G _ _ _ χ ψ hψ N r d g₀ hg hH2 hinj hH1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have hcont : ContAction (charRep (redChar ψ r)) := by
    apply contAction_charRep
    have e : (fun g => ((redChar ψ r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) =
        fun g => PadicInt.toZModPow r (ψ g : ℤ_[l]) := funext fun g => redChar_apply ψ r g
    rw [e]
    exact (continuous_toZModPow r).comp hψ
  have h1 := card_Z1_mul_card_H0 (charRep (redChar ψ r)) hcont
  obtain ⟨hfin0, hle0⟩ := card_invariants_twistedDual_charRep_le_pow χ ψ N r g₀ hg
  obtain ⟨e⟩ := hH2
  let F : H2 (charRep (redChar ψ r)) →
      (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+ ZMod (l ^ r)) :=
    fun c => (e.toLinearMap ∘ₗ
      (cup20 (redChar χ r) (charRep (redChar ψ r)) (MonoidHom.id G) c)).toAddMonoidHom
  have hF : Function.Injective F := by
    intro c c' hcc
    apply hinj
    apply LinearMap.ext
    intro y
    apply e.injective
    exact DFunLike.congr_fun hcc y
  have : Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+
      ZMod (l ^ r)) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (H2 (charRep (redChar ψ r))) := Finite.of_injective F hF
  have hc2 : Nat.card (H2 (charRep (redChar ψ r))) ≤ l ^ N :=
    ((Nat.card_le_card_of_injective F hF).trans
      (GlobalTheory.natCard_addMonoidHom_zmod_le (l ^ r) _)).trans hle0
  have hc2pos : 0 < Nat.card (H2 (charRep (redChar ψ r))) := Nat.card_pos
  have h0pos : 0 < Nat.card (H0 (charRep (redChar ψ r))) := Nat.card_pos
  have hZ : Nat.card (Z1 (charRep (redChar ψ r))) =
      l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d) := by
    apply Nat.eq_of_mul_eq_mul_right h0pos
    rw [h1, hH1, Nat.card_zmod]
    ring
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hZ]; positivity), ?_⟩
  rw [hZ]
  calc l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d)
      ≤ l ^ r * (l ^ N * (l ^ r) ^ d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc2)
    _ = l ^ N * l ^ (r * (d + 1)) := by ring

end GlobalTheory.Cyc.CocycleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.CocycleCount

theorem card_linear_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Module (ZMod N) A]
    [Finite A] : Finite (A →ₗ[ZMod N] ZMod N) ∧ Nat.card (A →ₗ[ZMod N] ZMod N) ≤ Nat.card A := by
  have h1 : Finite (A →ₗ[ZMod N] ZMod N) := DFunLike.finite _
  have h2 : Finite (A →+ ZMod N) := DFunLike.finite _
  refine ⟨h1, le_trans ?_ (GlobalTheory.natCard_addMonoidHom_zmod_le N A)⟩
  exact Nat.card_le_card_of_injective (fun f => f.toAddMonoidHom) LinearMap.toAddMonoidHom_injective

theorem card_H2_le (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Finite (ReciprocityTheory.Gal.H2 rho) ∧ Nat.card (ReciprocityTheory.Gal.H2 rho) ≤ Nat.card M := by
  have hT := card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  have hTc : Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) ≤ Nat.card M := hT.2
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  have hA := card_linear_le N A
  have hAc : Nat.card A ≤ Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have := hA.1
  refine ⟨Finite.of_equiv _ E.symm, ?_⟩
  rw [Nat.card_congr E]
  exact hA.2.trans (hAc.trans hTc)

theorem card_cocycles_mul_invariants_discrete (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) :
    Nat.card (ReciprocityTheory.Gal.Z1 rho) * Nat.card (ReciprocityTheory.Gal.H0 rho) =
      Nat.card (ReciprocityTheory.Gal.H1 rho) * Nat.card M := by
  have hle : ReciprocityTheory.Gal.B1 rho ≤ ReciprocityTheory.Gal.Z1 rho := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · exact (hrho.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [ReciprocityTheory.Gal.amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype)
  have h2 : Nat.card ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype) =
      Nat.card (ReciprocityTheory.Gal.B1 rho) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hk : LinearMap.ker (ReciprocityTheory.Gal.d0 rho) = ReciprocityTheory.Gal.H0 rho := by
    ext m
    rw [LinearMap.mem_ker, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [ReciprocityTheory.Gal.amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (ReciprocityTheory.Gal.d0 rho))
  have h4 : Nat.card (M ⧸ LinearMap.ker (ReciprocityTheory.Gal.d0 rho)) = Nat.card (ReciprocityTheory.Gal.B1 rho) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [h4, hk] at h3
  rw [h1, h2, h3]
  ring

def repOfAction (N : ℕ) {G M : Type} [Monoid G] [AddCommGroup M] [Module (ZMod N) M]
    (a : G → M →+ M) (h1 : ∀ m, a 1 m = m) (hmul : ∀ g h m, a (g * h) m = a g (a h m)) :
    Representation (ZMod N) G M where
  toFun g := AddMonoidHom.toZModLinearMap N (a g)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hmul g h)

theorem count_of_euler (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (hrho : ReciprocityTheory.Gal.ContAction rho)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m) :
    {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (d + 2) := by
  obtain ⟨hf2, hc2⟩ := card_H2_le _ _ M _ rho e hb
  have hZ := card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have h0 : 0 < Nat.card (ReciprocityTheory.Gal.H0 rho) := Nat.card_pos
  have h2 : 0 < Nat.card (ReciprocityTheory.Gal.H2 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hZ' : Nat.card (ReciprocityTheory.Gal.Z1 rho) =
      Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [hZ, hEu]
    ring
  let E : ↥{c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} ≃
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        (IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun g h => by
          have := c.2.2 (φ g) (φ h)
          rw [ha, φ.symm_apply_apply, ← map_mul] at this
          exact this⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) :=
    Nat.finite_of_card_ne_zero (by rw [hZ']; positivity)
  refine ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ E.symm), ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr E, hZ', pow_succ' _ (_ + 1)]
  exact Nat.mul_le_mul_right _ hc2

theorem cocycles_finite_ncard_le :
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, l ^ r • m = 0) → (∀ m, IsLocallyConstant fun g => a g m) → {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧ {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤ Nat.card M ^ (Module.finrank ℚ_[l] ↥K.1 + 2) := by
  intro hT hE l _ K r M _ _ a h1 hmul hr hlc
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  have hEu := hE l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  exact count_of_euler _ _ _ φ hφ M _ rho hrho e hb _ hEu a fun _ _ => rfl

end GlobalTheory.CocycleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulIdemFromCenter
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem exists_central_lift {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra B Γ)
    (hx : ∀ z, x * z = z * x) (hr : ∀ h, x.coeff h ∈ f.range) :
    ∃ z ∈ Subalgebra.center A (MonoidAlgebra A Γ), ∀ h : Γ, f (z.coeff h) = x.coeff h := by
  choose c hc using hr
  let z : MonoidAlgebra A Γ := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have hz : ∀ h, f (z.coeff h) = x.coeff h := fun h => hc h
  have hco : ∀ (y : MonoidAlgebra A Γ) h, (MonoidAlgebra.mapRingHom Γ f y).coeff h = f (y.coeff h) := by
    intro y h; simp
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom Γ f) := by
    intro a b hab
    ext h
    apply hf
    rw [← hco, ← hco, hab]
  have hzx : MonoidAlgebra.mapRingHom Γ f z = x := by
    ext h
    rw [hco, hz]
  refine ⟨z, ?_, hz⟩
  rw [Subalgebra.mem_center_iff]
  intro b
  apply hinj
  rw [map_mul, map_mul, hzx, hx]

theorem card_mul_idem_from_center : ∀ (D : D7) (i : D.nd.Loc) (Γ : Type) [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ), e * e = e → (∀ z, e * z = z * e) → (∃ ζ : D.nd.O i, IsPrimitiveRoot (iotaO D.nd D.naut i ζ) (Nat.card Γ)) → ∃ z ∈ Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) Γ), ∀ h : Γ, iotaO D.nd D.naut i (MonoidAlgebra.coeff z h) = (Nat.card Γ : ℂ) * e.coeff h := by
  intro D i Γ _ _ e he hc ⟨ζ, hζ⟩
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  have hco : ∀ h, ((Nat.card Γ : ℂ) • e).coeff h = (Nat.card Γ : ℂ) * e.coeff h := by
    intro h; simp
  obtain ⟨z, hz, hz'⟩ := exists_central_lift (iotaO D.nd D.naut i) hinj ((Nat.card Γ : ℂ) • e)
    (fun z => by rw [smul_mul_assoc, mul_smul_comm, hc]) (fun h => by
      rw [hco]
      have h1 := centralIdemCoeff Γ e he hc _ hζ h
      have h2 : Algebra.adjoin ℤ ({iotaO D.nd D.naut i ζ} : Set ℂ) ≤
          subalgebraOfSubring (iotaO D.nd D.naut i).range :=
        Algebra.adjoin_le (by rintro _ rfl; exact ⟨ζ, rfl⟩)
      exact h2 h1)
  exact ⟨z, hz, fun h => by rw [hz', hco]⟩

end GlobalTheory.CentralIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CartanDecomposition
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

theorem cartan_decomposition (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]) :
    ∃ (k k' : GL (Fin n) ℤ_[g]) (a : Fin n → ℤ), Antitone a ∧ (h : Matrix (Fin n) (Fin n) ℚ_[g]) =
      (inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) * Matrix.diagonal (fun i => (g : ℚ_[g]) ^ a i) *
        (inc g n k' : Matrix (Fin n) (Fin n) ℚ_[g]) := by
  have hP : IsPrincipalIdealRing (PadicInt.subring g) :=
    inferInstanceAs (IsPrincipalIdealRing ℤ_[g])
  have hg0 : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  obtain ⟨c, hc0, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ_[g])
    (fun ij : Fin n × Fin n => (h : Matrix (Fin n) (Fin n) ℚ_[g]) ij.1 ij.2) |>.imp
      (fun c hc => And.intro (nonZeroDivisors.coe_ne_zero c) hc)
  choose G hG using hc
  obtain ⟨a, ha, k₁, ⟨k, rfl⟩, k₂, ⟨k', rfl⟩, e⟩ :=
    Formalism.UG.P.cartan_decomp_gen (PadicInt.subring g) (NormedField.valuation (K := ℚ_[g]))
      (fun x => by
        rw [PadicInt.mem_subring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl)
      (g : ℚ_[g]) hg0
      (fun x hx => ⟨x.valuation, by
        apply NNReal.coe_injective
        rw [NormedField.valuation_apply, NormedField.valuation_apply, NNReal.coe_zpow, coe_nnnorm,
          coe_nnnorm, Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p, inv_zpow']⟩)
      h (c : ℤ_[g]) hc0 ⟨Matrix.of fun i j => G (i, j), by
        ext i j
        exact hG (i, j)⟩
  exact ⟨k, k', a, ha, e⟩

end GlobalTheory.GLp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  first | exact @GlobalTheory.GLq.ZOrth.zorth | exact GlobalTheory.GLq.ZOrth.zorth | (intros; apply GlobalTheory.GLq.ZOrth.zorth <;> assumption)
end

