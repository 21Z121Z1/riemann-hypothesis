import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCount
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem model_mul_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w), IsModel w e B u x γ → ∀ c : B.Aˣ, IsModel w e B u (x * ((c : B.A) * B.σ (c : B.A))) γ := by
  intro E _ _ _ w K e B u x n γ hM c
  obtain ⟨ψ, h1, h2, h3⟩ := hM
  let φ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    { toFun := fun y => ψ ((c : B.A) * y)
      invFun := fun v => ((c⁻¹ : B.Aˣ) : B.A) * ψ.symm v
      left_inv := fun y => by simp [← mul_assoc]
      right_inv := fun v => by simp [← mul_assoc]
      map_add' := fun y z => by simp [mul_add] }
  refine ⟨φ, fun a y => ?_, fun y => ?_, fun y z => ?_⟩
  · show ψ ((c : B.A) * (a • y)) = e a • ψ ((c : B.A) * y)
    rw [mul_smul_comm, h1]
  · show ψ ((c : B.A) * (u * y)) = γ.val *ᵥ ψ ((c : B.A) * y)
    rw [show (c : B.A) * (u * y) = u * ((c : B.A) * y) by ring, h2]
  · show stdH w (ψ ((c : B.A) * y)) (ψ ((c : B.A) * z)) = _
    rw [h3]
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 2
    rw [map_mul]
    ring

theorem kapOrb_eq_kapSum_of_fits {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w)
    {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hBr : Bridge w K e) {k : ℕ} {t : K.O} (ht : K.Small t)
    (htk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) {n : ℕ} {Q₁ Q₂ : (w.adicCompletion E)[X]}
    {B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K} {u₁ : B₁.A} {u₂ : B₂.A} (hsep : (Q₁ * Q₂).Separable) (hmon : (Q₁ * Q₂).Monic)
    (hdeg : (Q₁ * Q₂).natDegree = n) (hF₁ : Fits w e B₁ Q₁ u₁) (hF₂ : Fits w e B₂ Q₂ u₂)
    (hg : 1 + algebraMap K.O (B₁.prod B₂).A t * (B₁.prod B₂).g = (u₁, u₂)) :
    kapOrb n w Q₁ Q₂ (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) =
      ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  have hF := GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair E w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂
  unfold kapOrb clSum GlobalTheory.UnitLemma.InvAlg.kapSum
  rw [cast_finsum]
  set S' : Set (TwCl (MonoidHom.id (UL n w))) := {c | c.rep.1.val.charpoly = Q₁ * Q₂} with hS'
  have hex : ∀ c : TwCl (MonoidHom.id (UL n w)), c ∈ S' → ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧
      IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 := fun c hc =>
    GlobalTheory.T.exists_hermitianMultiplicationModel_nonsplit E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) (u₁, u₂) hsep hF c.rep.1 c.rep.2 hc
  let Φ : TwCl (MonoidHom.id (UL n w)) → (B₁.prod B₂).Cl := fun c =>
    if h : ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧ IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 then
      Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ else Quot.mk _ ⟨1, by simp⟩
  have hrep : ∀ c ∈ S', IsModel w e (B₁.prod B₂) (u₁, u₂) (GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c)) c.rep.1 := by
    intro c hc
    have h := hex c hc
    have hΦ : Φ c = Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ := dif_pos h
    have hq := Quot.eqvGen_exact ((Quot.out_eq (Φ c)).trans hΦ)
    obtain ⟨v, hv⟩ := (clRel_equiv (B₁.prod B₂)).symm ((clRel_equiv (B₁.prod B₂)).eqvGen_iff.1 hq)
    have hr : GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c) = h.choose * ((v : (B₁.prod B₂).A) * (B₁.prod B₂).σ (v : (B₁.prod B₂).A)) := by
      unfold GlobalTheory.UnitLemma.InvAlg.Cl.rep
      rw [hv]
      simp
    rw [hr]
    exact model_mul_norm E w K e (B₁.prod B₂) _ _ n _ h.choose_spec.2.2 v
  let G : (B₁.prod B₂).Cl → ℂ := fun κ =>
    ((K.eta (B₁.gramDet (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ).1) * (B₁.prod B₂).N κ.rep : ℚ) : ℂ)
  have hterm : ∀ c ∈ S', kapSign n w Q₁ c.rep.1 * twOrb (MonoidHom.id (UL n w)) (KL n w) c.rep
      (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = G (Φ c) := by
    intro c hc
    have hm := hrep c hc
    have h7 := GlobalTheory.T.twisted_orbitalIntegral_congruence_level_eq_count E w hw K e hBr k t ht htk n (Q₁ * Q₂) (B₁.prod B₂) _ _ hsep hF hg.symm c.rep.1 c.rep.2 hm
    simp only [Subtype.coe_eta] at h7
    rw [GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet E w hw K e hBr n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ _ _ hm, h7]
    simp [G]
  have hinj : Set.InjOn Φ S' := by
    intro c₁ hc₁ c₂ hc₂ h12
    have m₁ := hrep c₁ hc₁
    have m₂ := hrep c₂ hc₂
    rw [h12] at m₁
    obtain ⟨y, hy, hyc⟩ := GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel E w hw K e (B₁.prod B₂) _ _ n _ _ m₁ m₂
    rw [← Quot.out_eq c₁, ← Quot.out_eq c₂]
    exact Quot.sound ⟨⟨y, hy⟩, Subtype.ext (by simpa [TwCl.rep] using hyc)⟩
  have hsupp : Function.support G ⊆ Φ '' S' := by
    intro κ hκ
    have hN : (B₁.prod B₂).N κ.rep ≠ 0 := by
      intro h0; apply hκ; simp [G, h0]
    have hfix : (B₁.prod B₂).σ (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) = GlobalTheory.UnitLemma.InvAlg.Cl.rep κ := (Quot.out κ).2
    have hunit : IsUnit (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) := (Quot.out κ).1.isUnit
    obtain ⟨γ, hγ, hmγ⟩ := GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) _ _ hF hdeg hfix hunit hN
    have hcp : γ.val.charpoly = Q₁ * Q₂ := GlobalTheory.T.charpoly_eq_of_hermitianMultiplicationModel E w K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ γ hmon hF hmγ
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ ⟨γ, hγ⟩
    obtain ⟨g, hg'⟩ := (conjRel_equiv (UL n w)).symm
      ((conjRel_equiv (UL n w)).eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq c)))
    have hcrep : c.rep.1 = g.1⁻¹ * γ * g.1 := by
      have := congrArg Subtype.val hg'
      simpa [TwCl.rep] using this
    have hc : c ∈ S' := by
      show c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcrep, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hcp]
    refine ⟨c, hc, ?_⟩
    have m := hrep c hc
    rw [hcrep] at m
    obtain ⟨v, hv⟩ := GlobalTheory.T.hermitianModels_conj_unitary_differ_by_norm E w hw K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ _ hsep hF γ g.1 g.2 hmγ m
    exact (Quot.out_eq (Φ c)).symm.trans ((Quot.sound ((clRel_equiv _).symm ⟨v, hv⟩)).trans (Quot.out_eq κ))
  calc _ = ∑ᶠ c, S'.indicator (fun c => G (Φ c)) c := finsum_congr fun c => by
          by_cases hc : c ∈ S'
          · rw [Set.indicator_of_mem hc, ← hterm c hc]
            exact if_pos hc
          · rw [Set.indicator_of_notMem hc]
            exact if_neg hc
    _ = ∑ᶠ c ∈ S', G (Φ c) := (finsum_mem_def _ _).symm
    _ = ∑ᶠ κ ∈ Φ '' S', G κ := (finsum_mem_image hinj).symm
    _ = ∑ᶠ κ, G κ := by
      exact (finsum_mem_inter_support_eq G (Φ '' S') Set.univ (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp])).trans
        (finsum_mem_univ G)

theorem kapOrb_congruence_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he1 he2 he3 he4 k t ht htk n a b Q₁ Q₂ B₁ B₂ hab hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
    hadj₁ hae₁ hfr₁ hu₁ hadj₂ hae₂ hfr₂ hu₂
  exact kapOrb_eq_kapSum_of_fits hw ⟨he1, he2, he3, he4⟩ ht htk hsep (hm₁.mul hm₂)
    (by rw [hm₁.natDegree_mul hm₂, hd₁, hd₂, hab]) ⟨hadj₁, hae₁, hfr₁, hu₁⟩ ⟨hadj₂, hae₂, hfr₂, hu₂⟩ (Prod.ext rfl rfl)

end GlobalTheory.KapLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfFst
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Points

namespace GlobalTheory.UnifImmersive

theorem primeSpectrum_eq (x x' : PrimeSpectrum (DualNumber ℂ)) : x = x' := by
  have H (p : PrimeSpectrum (DualNumber ℂ)) : Ideal.span {DualNumber.eps} = p.asIdeal :=
    DualNumber.isMaximal_span_singleton_eps.eq_of_le p.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).2 (p.isPrime.mem_of_pow_mem 2 (by simp [sq])))
  exact PrimeSpectrum.ext ((H x).symm.trans (H x'))

theorem le_preimage_of_fst {X : Scheme.{0}} (t : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t) ⁻¹ᵁ U) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro x _
  have hx := h (x := IsLocalRing.closedPoint ℂ) trivial
  have e : x = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ) :=
    primeSpectrum_eq _ _
  rw [e]
  exact hx

theorem eq_const {X : Scheme.{0}} (t : Sp (DualNumber ℂ) ⟶ X) (o : Sp ℂ ⟶ X)
    (ho : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t = o)
    (H : ∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ o ⁻¹ᵁ U → TrivSqZeroExt.snd (valR t U f) = 0) :
    t = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ o := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := o (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  have h₀ : ⊤ ≤ o ⁻¹ᵁ U := fun z _ => by
    rwa [show z = IsLocalRing.closedPoint ℂ from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
  have h₁ : ⊤ ≤ t ⁻¹ᵁ U := le_preimage_of_fst t U (ho ▸ h₀)
  refine ext_of_valR hU h₁ (le_preimage_comp _ o h₀ le_top) fun f => ?_
  rw [valR_spMap_comp _ o U h₀, ← ho, valR_spMap_comp _ t U h₁]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, H U f h₀]

theorem eq_zero_of_cov : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y),
    ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧
      (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) →
    ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)),
      ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0 := by
  intro S P y d ⟨h₁, h₂⟩ w hw
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
  let t : Sp (DualNumber ℂ) ⟶ d.B.left := v.left
  have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t = LieVB.unitSec d.B := hv
  have hb : t ≫ d.B.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
  have hu : LieVB.unitSec d.B ≫ d.φ = y ≫ LieVB.unitSec P.A := LieVB.unitSec_comp d.isPull
  have ho : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t ≫ d.φ = y ≫ LieVB.unitSec P.A := by
    rw [← Category.assoc, ht, hu]
  have e₁ := eq_const (t ≫ d.φ) _ ho fun W f hW => by
    have hW' : ⊤ ≤ t ⁻¹ᵁ d.φ ⁻¹ᵁ W := le_preimage_of_fst (t ≫ d.φ) W (ho ▸ hW)
    rw [valR_comp, valR_eq _ _ hW']
    refine (hd (d.φ ⁻¹ᵁ W) hW' (d.φ.app W f)).trans (Eq.trans ?_ (hw W f hW))
    have e : (fun z => valAt' (d.u.ex z).left (d.φ ⁻¹ᵁ W) (d.φ.app W f)) = d.fn W f :=
      funext fun z => (valR_comp _ _ _ _).symm
    rw [e]
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Pi.single a (w a) : Fin P.g → ℂ) = w a • Pi.single a 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
    rfl
  have e₂ : t = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ LieVB.unitSec d.B := by
    refine d.isPull.1.hom_ext ?_ ?_
    · rw [e₁, Category.assoc, hu]
    · rw [hb, Category.assoc, LieVB.sec_hom, Category.comp_id]
  refine (h₁ v hv).unique hd fun U h f => ?_
  have h₀ : ⊤ ≤ LieVB.unitSec d.B ⁻¹ᵁ U := ht ▸ le_preimage_comp _ t h le_top
  rw [map_zero]
  refine (congrArg TrivSqZeroExt.snd (valR_eq t U h f)).symm.trans ?_
  rw [e₂, valR_spMap_comp _ _ U h₀]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.UnifImmersive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUnique
section
noncomputable section

namespace GlobalTheory.LevelFree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem eta_injective (Xo : Moduli Dw l) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (β : KA l →+* k)
    (hx : x ≫ Xo.s = spMap β) (a : Dw.La) (h : toUnit (Over.mk x) ≫ Xo.univ.eta a = 1) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom k x β hx
  have htop : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) = ⊤ := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [htop]; trivial
  obtain ⟨a₂, h₂, a₁, h₁, rfl⟩ := Submodule.mem_sup.1 ha
  have e : toUnit (Over.mk x) ≫ Xo.univ.eta (a₂ + a₁) = toUnit (Over.mk x) ≫ Xo.univ.eta a₁ := by
    rw [Xo.univ.eta_add, Xo.univ.eta_ker a₂ h₂, _root_.one_mul]
  have e₁ : I.ev l.M a₁ = 1 := (hI a₁ h₁).symm.trans (e.symm.trans h)
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨b, rfl⟩ := (I.ker l.M hM a₁).1 e₁
  have hMm : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact hle this
  refine Submodule.add_mem _ h₂ ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hMm trivial

section Bridge

abbrev fib {X Y : Scheme.{0}} (G : Over X) (x : Y ⟶ X) : Over Y := (Over.pullback x).obj G

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

def pushAt {ρ : X ⟶ X} {F : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (T : Over X) (c : T.left ⟶ X)
    (e : T.hom ≫ ρ = c) : (T ⟶ G) →* (Over.mk c ⟶ G) :=
  MonoidHom.mk' (fun u => Over.homMk (u.left ≫ F) (by
      subst e
      show (u.left ≫ F) ≫ G.hom = T.hom ≫ ρ
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u])) (fun a b => by
    subst e
    exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm)

theorem one_left_congr {T : Scheme.{0}} {c c' : T ⟶ X} (h : c = c') :
    (1 : Over.mk c ⟶ G).left = (1 : Over.mk c' ⟶ G).left := by
  subst h; rfl

end Bridge

theorem sections_eq {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) [IsProper G.hom]
    {ρ ρ' : X ⟶ X} {F F' : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (h' : IsGrpPullback G G ρ' F')
    {k : Type} [Field k] [CharZero k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x ≫ ρ')
    (ht : ∀ w : overAt x (DualNumber k) ⟶ G, smT x 0 w = 1 → w.left ≫ F = w.left ≫ F')
    (s : Over.mk x ⟶ G) : s.left ≫ F = s.left ≫ F' := by
  have pA : IsGrpPullback (fib G x) G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have pB : IsGrpPullback (fib G (x ≫ ρ)) G (x ≫ ρ) (pullback.fst G.hom (x ≫ ρ)) := isGrpPullback_pullback G (x ≫ ρ)
  have c₁ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F) := IsGrpPullback.comp pA h
  have c₂ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F') := hx ▸ IsGrpPullback.comp pA h'
  let f : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F) (pullback.snd G.hom x) c₁.1.w) (pullback.lift_snd _ _ _)
  let f' : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F') (pullback.snd G.hom x) c₂.1.w) (pullback.lift_snd _ _ _)
  have ef : f.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F := pullback.lift_fst _ _ _
  have ef' : f'.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F' := pullback.lift_fst _ _ _
  haveI : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pB (𝟙 G) f (by simpa using ef)
  haveI : IsMonHom f' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₂ pB (𝟙 G) f' (by simpa using ef')
  have hA : IsAbelianScheme (fib G x) := by
    haveI : IsProper (fib G x).hom := inferInstanceAs (IsProper (pullback.snd G.hom x))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback x G hG)
  have hB : IsAbelianScheme (fib G (x ≫ ρ)) := by
    haveI : IsProper (fib G (x ≫ ρ)).hom := inferInstanceAs (IsProper (pullback.snd G.hom (x ≫ ρ)))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback (x ≫ ρ) G hG)
  haveI : IsCommMonObj (fib G x) := hA.comm
  haveI : IsCommMonObj (fib G (x ≫ ρ)) := hB.comm
  have key : f = f' := by
    refine GlobalTheory.T.abelianScheme_hom_eq_of_tangent_eq k _ _ hA hB f f' fun v hv => ?_
    let w : overAt x (DualNumber k) ⟶ G := Over.homMk (v.left ≫ pullback.fst G.hom x) (by
      have e := Over.w v
      show (v.left ≫ pullback.fst G.hom x) ≫ G.hom = spMap (algebraMap k (DualNumber k)) ≫ x
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have e' : v.left ≫ pullback.snd G.hom x = spMap (algebraMap k (DualNumber k)) ≫ 𝟙 (Sp k) := e
      rw [e', Category.comp_id])
    have hw : smT x 0 w = 1 := by
      apply Over.OverMorphism.ext
      have e₁ : (smT x 0 w).left = (smT (𝟙 (Sp k)) 0 v).left ≫ pullback.fst G.hom x := by
        simp only [smT_left, w, Over.homMk_left, Category.assoc]
      rw [e₁, hv]
      have e₂ := congrArg (fun z => z.left) (map_one (pushHom pA (overAt (𝟙 (Sp k)) (DualNumber k))))
      refine e₂.trans (one_left_congr ?_)
      simp
    have e := ht w hw
    apply Over.OverMorphism.ext
    refine pB.1.hom_ext ?_ ?_
    · simp only [Over.comp_left, Category.assoc]
      rw [ef, ef']
      simpa [w] using e
    · rw [Over.w, Over.w]
  let a : Over.mk (𝟙 (Sp k)) ⟶ fib G x := Over.homMk (pullback.lift s.left (𝟙 _) (by simpa using Over.w s)) (pullback.lift_snd _ _ _)
  have ea : a.left ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
  have e1 : a.left ≫ f.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F := by
    rw [ef, ← Category.assoc, ea]
  have e2 : a.left ≫ f'.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F' := by
    rw [ef', ← Category.assoc, ea]
  rw [← e1, ← e2, key]

theorem move_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (g g' : Gam Dw l), levR (lift g, LinearMap.id) y y' → levR (lift g', LinearMap.id) y y' → g = g' := by
  intro E _ _ _ H Dw l Xo c _ _ lift hl k _ _ _ y y' g g' h h'
  obtain ⟨ρ, ν, -, hm, hf⟩ := h
  obtain ⟨ρ', ν', -, hm', hf'⟩ := h'
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  haveI : IsProper Xo.univ.t.G.hom := Xo.univ.proper
  have hx : y.x ≫ ρ = y.x ≫ ρ' := hf.1.symm.trans hf'.1
  have hu : ∀ τ i, y.u τ i ≫ ν.φ = y.u τ i ≫ ν'.φ := fun τ i => (hf.2.1 τ i).symm.trans (hf'.2.1 τ i)
  have ht : ∀ w : overAt y.x (DualNumber k) ⟶ Xo.univ.t.G, smT y.x 0 w = 1 → w.left ≫ ν.φ = w.left ≫ ν'.φ := by
    intro w hw
    have hT : IsTanAt y.x w.left := isTanAtG_of (t := Xo.univ.t) w hw
    obtain ⟨a, ⟨u, hu1, hu2⟩, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan.frTanBasis_holds Xo c k y w.left hT
    let P := pushAt ν.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ) rfl
    let P' := pushAt ν'.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ)
      (by simp only [Over.mk_hom, Category.assoc, hx])
    have e₁ : ∀ i, P (u i) = P' (u i) := fun i => by
      apply Over.OverMorphism.ext
      show (u i).left ≫ ν.φ = (u i).left ≫ ν'.φ
      rw [hu1, Category.assoc, Category.assoc, hu]
    have e₂ : P (List.ofFn u).prod = P' (List.ofFn u).prod := by
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 2
      exact funext e₁
    have e₃ := congrArg (fun z => z.left) e₂
    have e₄ : ((List.ofFn u).prod).left ≫ ν.φ = ((List.ofFn u).prod).left ≫ ν'.φ := e₃
    rw [hu2] at e₄
    exact e₄
  have hs := sections_eq Xo.univ.t.semi ν.cart ν'.cart y.x hx ht
  have tl : (toUnit (Over.mk y.x)).left = y.x := by simpa using Over.w (toUnit (Over.mk y.x))
  have hη : ∀ a, toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) = toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a) := by
    intro a
    have e₁ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a)).left ≫ ν.φ = y.x ≫ ρ ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm.2.1 a]
    have e₂ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)).left ≫ ν'.φ = y.x ≫ ρ' ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm'.2.1 a]
    apply Over.OverMorphism.ext
    refine ν.cart.1.hom_ext ?_ ?_
    · rw [e₁, hs, e₂, ← Category.assoc, ← Category.assoc, hx]
    · rw [Over.w, Over.w]
  have hz : ∀ a, lift g a - lift g' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    intro a
    refine eta_injective Xo y.x ((algebraMap c.F k).comp (IntermediateField.inclusion c.le).toRingHom) y.x_over _ ?_
    have e : toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) =
        (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a - lift g' a)) * (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)) := by
      rw [← MonObj.comp_mul, ← Xo.univ.eta_add, sub_add_cancel]
    rw [hη a] at e
    exact (mul_eq_right.1 e.symm)
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e₁ := LinearMap.congr_fun (hl g) a
  have e₂ := LinearMap.congr_fun (hl g') a
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at e₁ e₂
  rw [← e₁, ← e₂]
  exact (Submodule.Quotient.eq _).2 (hz a)

end GlobalTheory.LevelFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.LieSecondPf

theorem lieSecond_of_lieScalar : GlobalTheory.FunPr.Hypotheses₂ → DerEx → FockEx → VacLine → LieScalar → LieSecond := by
  intro _ hD hF hV hL F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hCM hψ hFr hΦ hW hχ
  obtain ⟨hU, dd, omd, hdd, hWS, hres⟩ := hW
  obtain ⟨c, hc⟩ := hL F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hU
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  obtain ⟨Φd, hΦd⟩ := hF F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) hCM hψ hFrd
  obtain ⟨cd, hcd⟩ := hL F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd omd hCM hψ hFrd hΦd hWS.2.1
  have key : ∀ w (Y : Mat R S), c w * Y.trace = (m w : ℂ) / 2 * Y.trace := by
    intro w Y
    rcases Nat.eq_zero_or_pos (R + S) with h0 | hpos
    · have hR : R = 0 := by omega
      have hS : S = 0 := by omega
      subst hR hS
      have : Y.trace = 0 := by simp [Matrix.trace]
      rw [this, mul_zero, mul_zero]
    · have hbox := GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj hD hV F E σ α β κ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
      have hl := GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian F E σ α β κ ψ JA JB d dd hψ hdd
      have hne : (∫ x : κ → mixedEmbedding.mixedSpace F,
          Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 := by
        obtain ⟨z, hz, hzx⟩ := hbox
        have h1 : ∀ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) =
            z * (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x * star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x)) := by
          intro x
          rw [hzx, Sum.elim_comp_inl, Sum.elim_comp_inr, mul_assoc]
        simp_rw [h1]
        rw [MeasureTheory.integral_const_mul]
        refine mul_ne_zero hz (GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero F κ _ ?_)
        intro h0
        exact GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (by rw [h0, map_zero]))
      have h1 := GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces F E σ α β κ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hcd hl hne hpos w
      have h2 := GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hCM hψ hΦ hres hc hcd hbox hpos w
      rw [h2, h1]
  intro γ hγ Y hY T
  have e : (fun w => fockAct2 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) =
      fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1 := by
    funext w
    rw [key w (Y w)]
  have := hc γ hγ Y hY T
  rw [← e] at this
  exact this

end GlobalTheory.RealLift.LieSecondPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemHilbertFunctionEqFinrankConePiece
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

namespace GlobalTheory.DegCmp

theorem rank_map_eq_of_ker_iff {K M A B : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (S : Submodule K M) (f : M →ₗ[K] A) (g : M →ₗ[K] B)
    (h : ∀ x ∈ S, f x = 0 ↔ g x = 0) :
    Module.rank K (S.map f) = Module.rank K (S.map g) := by
  have hk : LinearMap.ker (f.domRestrict S) = LinearMap.ker (g.domRestrict S) := by
    ext x
    simpa using h x x.2
  rw [← LinearMap.range_domRestrict, ← LinearMap.range_domRestrict,
    ← (LinearMap.quotKerEquivRange _).rank_eq, ← (LinearMap.quotKerEquivRange _).rank_eq, hk]

theorem range_pow_eq_map_homogeneous {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) (τ : ℕ) :
    ((LinearMap.range ev) ^ τ : Submodule K Ω) =
      (homogeneousSubmodule (Fin N) K τ).map (aeval (fun j => ev (b j)) : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← homogeneousSubmodule_one_pow, Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span,
    LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 3
  ext j
  simp

theorem hilb_eq_finrank_quotPiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  intro K V Ω _ _ _ _ _ ev N b τ
  rw [hilb, range_pow_eq_map_homogeneous ev b τ, GlobalTheory.quotPiece_natCast,
    rank_map_eq_of_ker_iff _ _ (Ideal.Quotient.mkₐ K (imageIdeal ev b)).toLinearMap, ← Module.finrank_eq_rank]
  · simp
  · intro x hx
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_coneIdeal_of_isHomogeneous _ hx).symm

end GlobalTheory.DegCmp
end

