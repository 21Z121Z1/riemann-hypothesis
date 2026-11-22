import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0083
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0133
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallCoeffFieldEmbeddingCompHostMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0937
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolume
section
set_option autoImplicit false

namespace GlobalTheory.ConjScalar

section Ideals

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.HeckeIdealValue
open scoped nonZeroDivisors

variable {L : Type} [Field L] [NumberField L]

theorem conj_of_primes (χ χ' : HChar L) (τ : ℂ ≃+* ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      τ (((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ)) =
        ((χ'.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ))
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    τ (((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)) =
      ((χ'.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have key : ∀ ψ : HChar L,
        ((ψ.onId ((p * a : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) *
          ((Real.sqrt (Ideal.absNorm (p * a) : ℝ) : ℝ) : ℂ) =
        (((ψ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ)) *
          (((ψ.onId (a : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm a : ℝ) : ℝ) : ℂ)) := fun ψ => by
      rw [FractionalIdeal.coeIdeal_mul, onId_mul ψ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
        (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
        show ψ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = ψ.val v from onId_prime ψ v]
      push_cast
      ring
    rw [key, key, map_mul, h v hb, ih ha ha1]

end Ideals

section Lattice

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_numerator_coprime (H : Host E) {n bad : ℕ} (Λ : GenLat E n) (hU : Λ.Unimod) (hT : Λ.TrivAt bad) :
    ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ ∧ cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      Submodule.span (𝓞 E) (detSet Λ.La) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  obtain ⟨h0, cc, c1, c2, c3⟩ := GlobalTheory.ScalarUnit.exists_numerator H Λ hU
  have hN : Nat.Coprime (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index bad := by
    refine Nat.coprime_of_dvd fun p hp h1 h2 => ?_
    obtain ⟨k, hk, hk'⟩ := hT
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (GlobalTheory.ScalarUnit.index_coprime hp Λ ⟨k, hk.coprime_dvd_right h2, hk'⟩ h0).symm h1
  generalize (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index = N at *
  refine ⟨cc, fun e => h0 ?_, ?_, c1, c2⟩
  · rw [e, Ideal.mem_bot] at c3
    exact_mod_cast c3
  · obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 E))
    simp only [map_natCast] at e
    rw [Ideal.eq_top_iff_one, ← e]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ c3))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem ep_conj {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n bad : ℕ} (ta : c.F ≃+* c.F)
    {B B' : Ideal (𝓞 E) → c.F} {epF epF' : Submodule (𝓞 E) (Fin n → E) → c.F}
    (he : EpIs (Dw := Dw) c bad B epF) (he' : EpIs (Dw := Dw) c bad B' epF')
    (hB : ∀ cc, cc ≠ ⊥ → cc ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ → ta (B cc) = B' cc)
    {L : Submodule (𝓞 E) (Fin n → E)} (g : GlobalTheory.ClassScalarCompare.Guard H bad L) : ta (epF L) = epF' L := by
  obtain ⟨cc, c0, c1, c2, c3⟩ := exists_numerator_coprime H ⟨L⟩ g.1 g.2.1
  obtain ⟨q, q0, q1, q2⟩ := he L cc g.1 g.2.1 g.2.2 c2 c3
  obtain ⟨q', q0', q1', q2'⟩ := he' L cc g.1 g.2.1 g.2.2 c2 c3
  have hN : (Ideal.absNorm cc : ℚ) ≠ 0 := by exact_mod_cast fun h => c0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hq : q = q' := by
    have h1 := q1.trans q1'.symm
    rw [← q1] at hN
    exact (pow_left_inj₀ q0.le q0'.le two_ne_zero).1 (mul_right_cancel₀ (right_ne_zero_of_mul hN) h1)
  rw [q2, q2', map_mul, map_inv₀, hB cc c0 c1, map_ratCast, hq]

end Lattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in

theorem conj_vol_ep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ta (M.vol a) = M.vol b ∧ ∀ k, ta (M.ep a k) = M.ep b (e k) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hO τ ta hta hF a b e hS hab
  obtain ⟨-, -, -, hbad, hvol, hk⟩ := hS
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨h, J', hR, -⟩ := (hO.tuple a).reps
    rw [hvol, hR.2.2.2.2.1, map_inv₀, map_natCast]
  · have hxi := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hC τ (tup a) (tup b) hab).2.2.1
    obtain ⟨r1, r2, -, -, -, r6⟩ := (hO.reps a).1 k
    have hcj := (GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps a).2 k
    have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (M.La a k).La) ⟨r1, r2, r6⟩
    rw [hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat] at g
    have heb := (hO.ep b).2
    have hBb := (hO.tuple b).B
    rw [hbad] at heb hBb
    rw [(hO.ep a).1 k, (hO.ep b).1 (e k), (hk k).1]
    refine ep_conj M.c' ta (hO.ep a).2 heb (fun cc c0 c1 => Subtype.ext ?_) g
    have h1 : ((M.B a cc : M.c'.F) : ℂ) = _ := (hO.tuple a).B cc c0 c1
    have h2 : ((M.B b cc : M.c'.F) : ℂ) = _ := hBb cc c0 c1
    rw [hta, h1, h2]
    refine conj_of_primes _ _ τ _ (fun P hP => ?_) cc c0 c1
    have hs := hF.split P fun hj => hP (by
      obtain ⟨u, hu⟩ := (hO.bad a).2.2.2.2
      rw [hu, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hj)
    have key : ∀ t, (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val P : ℂˣ) : ℂ) *
        ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) = (((R.xiH t).val P : ℂˣ) : ℂ) *
        ((((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)) := fun t => by
      simp only [Formalism.L2.Host.HChar.val_mul, Units.val_mul]
      ring
    rw [key, key, map_mul, hs, hxi]

end GlobalTheory.ConjScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyCon
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbLC

theorem eventually_eq_fun {A G β : Type} [TopologicalSpace A] [TopologicalSpace G] (Φ : A → G → β) (a₀ : A)
    (K : Set G) (hK : IsCompact K) (hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g)
    (hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g) : ∀ᶠ a in 𝓝 a₀, Φ a = Φ a₀ := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := a₀) (P := fun a g => Φ a g = Φ a₀ g) (by
    intro g hg
    have h1 := hloc g hg
    have hT : Tendsto (fun z : A × G => (a₀, z.2)) (𝓝 (a₀, g)) (𝓝 (a₀, g)) := by
      have : Continuous (fun z : A × G => (a₀, z.2)) := by fun_prop
      simpa using this.tendsto (a₀, g)
    have h2 := hT.eventually h1
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2])
  filter_upwards [h, hout] with a h1 h2
  funext g
  by_cases hg : g ∈ K
  · exact h1 g hg
  · exact h2 g hg

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, Units.val_mul, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  simp only [actU]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · apply Subtype.ext
    simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem part1 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F) :
    orbG M f' (act g Y) = orbG M f' Y := by
  letI := M.mG
  haveI := M.bG
  haveI := GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified F E r M
  unfold orbG
  simp only [← act_mul]
  exact integral_mul_right_eq_self (fun h => f' (act h Y) * omega (act h Y)) g

theorem part2 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) :
    orbU M f (actU g X) = orbU M f X := by
  letI := M.mU
  haveI := M.bU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  unfold orbU
  simp only [← actU_mul]
  exact integral_mul_right_eq_self (fun h => f (actU h X)) g

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem companion_pow_mulVec {r : ℕ} {k : Type} [CommRing k] (p : Fin r → k) :
    ∀ (j : ℕ) (hj : j < r), (companion p) ^ j *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) =
      Pi.single (⟨j, hj⟩ : Fin r) 1 := by
  intro j
  induction j with
  | zero =>
    intro hj
    funext i
    simp only [pow_zero, Matrix.one_mulVec, Pi.single_apply, Fin.ext_iff]
  | succ j ih =>
    intro hj
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
    funext i
    rw [Matrix.mulVec_single]
    simp only [companion, Matrix.of_apply, mul_one, Pi.single_apply, Fin.ext_iff]
    have : j + 1 ≠ r := by omega
    simp [this]

theorem Cm_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, Matrix.of_apply]
  rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h := companion_pow_mulVec a.1 j j.2
  simp only [sec] at h ⊢
  rw [h, Fin.eta, dotProduct_single, mul_one]

theorem lastDet_act_sec {r : ℕ} {k : Type} [CommRing k] (g : GL (Fin r) k) (a : Inv r k) :
    lastDet (act g (sec a)) = (-1) ^ r * (Delta a * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).det) := by
  rw [(GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det k r).1, (GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det k r).2, Matrix.det_mul, Cm_sec]
  rfl

theorem eta_eventually {F : Type} [NormedField F] [IsUltrametricDist F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, eta y = eta x := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  have hn : ‖y‖ = ‖x‖ := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hy.ne
    rw [sub_add_cancel] at this
    rw [this, max_eq_right hy.le]
  unfold eta
  rw [hn]

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem part3 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (hf : IsTest f') (a₀ : Inv r F) (hΔ : Delta a₀ ≠ 0) :
    ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀) := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨hcont, -, hDc, hprop⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hopen : IsOpen {a : Inv r F | Delta a ≠ 0} := isOpen_ne_fun hDc continuous_const
  obtain ⟨Ω, hΩn, hΩsub, hΩc⟩ := local_compact_nhds (hopen.mem_nhds hΔ)
  set K : Set (GL (Fin r) F) :=
    Prod.fst '' {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ tsupport f'} with hKdef
  have hK : IsCompact K := (hprop (tsupport f') Ω hf.2 hΩc (fun a ha => hΩsub ha)).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f' (act g (sec a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → GL (Fin r) F → ℂ := fun a g => f' (act g (sec a)) * omega (act g (sec a)) with hΦ
  have ha₀ : a₀ ∈ Ω := mem_of_mem_nhds hΩn
  have hc2 : Continuous (fun z : Inv r F × GL (Fin r) F => act z.2 (sec z.1)) :=
    hcont.comp continuous_swap
  have hdet : Continuous (fun z : Inv r F × GL (Fin r) F =>
      (-1 : F) ^ r * (Delta z.1 * ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det)) := by
    have h1 : Continuous (fun z : Inv r F × GL (Fin r) F => ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_snd)
    exact continuous_const.mul ((hDc.comp continuous_fst).mul h1.matrix_det)
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have h1 : ∀ᶠ z in 𝓝 (a₀, g), f' (act z.2 (sec z.1)) = f' (act g (sec a₀)) :=
      (hc2.tendsto (a₀, g)).eventually ((IsLocallyConstant.iff_eventually_eq f').1 hf.1 _)
    have hne : (-1 : F) ^ r * (Delta a₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hΔ ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g⁻¹ : GL (Fin r) F))).ne_zero
    have h2 := (hdet.tendsto (a₀, g)).eventually (eta_eventually _ hne)
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hΦ, omega, lastDet_act_sec]
    rw [hz1]
    rw [hz2]
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩn] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg, zero_mul]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout] with a h
  have h' : ∀ g, f' (act g (sec a)) * omega (act g (sec a)) = f' (act g (sec a₀)) * omega (act g (sec a₀)) :=
    fun g => congrFun h g
  simp only [orbG, h']

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem continuous_star_of_unram (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] : Continuous (star : E → E) :=
  (AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) (fun x => Unram.norm_star (F := F) x)).continuous

theorem continuous_actU (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2) := by
  haveI : ContinuousStar E := ⟨continuous_star_of_unram F E⟩
  have hg : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hb : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hl : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk (hg.matrix_mulVec hb) hl)
  exact Continuous.subtype_mk ((hg.mul hA).mul hg.star) _

theorem part4 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (hf : IsTest f) (a₀ : Inv r F) (X₀ : Hn r F E)
    (hΔ : Delta a₀ ≠ 0) (hX₀ : HasInv X₀ a₀) :
    ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  obtain ⟨Ω, s, hΩc, hΩo, ha₀, hs, hsinv, hprop⟩ := (GlobalTheory.T.invariant_image_openClosed_local_sections F E r a₀ hΔ).2 ⟨X₀, hX₀⟩
  have huniq := (GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r).2.2.1
  set K : Set (Matrix.unitaryGroup (Fin r) E) :=
    Prod.fst '' {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ tsupport f} with hKdef
  have hK : IsCompact K := (hprop (tsupport f) hf.2).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f (actU g (s a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → Matrix.unitaryGroup (Fin r) E → ℂ := fun a g => f (actU g (s a)) with hΦ
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have hsa : ContinuousAt s a₀ := hs.continuousAt (hΩo.mem_nhds ha₀)
    have h1 : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1)) (a₀, g) :=
      continuousAt_snd.prodMk (hsa.comp continuousAt_fst)
    have hT : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => actU z.2 (s z.1)) (a₀, g) :=
      ContinuousAt.comp (g := fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2)
        (f := fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1))
        ((continuous_actU F E r).continuousAt) h1
    exact hT.tendsto.eventually ((IsLocallyConstant.iff_eventually_eq f).1 hf.1 _)
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩo.mem_nhds ha₀] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg]
  have horb : ∀ a ∈ Ω, ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f (s a) := by
    intro a ha X hX
    obtain ⟨g, hg, -⟩ := huniq (s a) X a (hsinv a ha).1 (hsinv a ha).2 hX
    rw [← hg, part2]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout, hΩo.mem_nhds ha₀] with a h ha
  refine ⟨⟨s a, (hsinv a ha).2⟩, fun X hX => ?_⟩
  have h' : ∀ g, f (actU g (s a)) = f (actU g (s a₀)) := fun g => congrFun h g
  rw [horb a ha X hX, horb a₀ ha₀ X₀ hX₀]
  simp only [orbU, h']

theorem orbital_integrals_invariant_locally_constant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F), orbG M f' (act g Y) = orbG M f' Y) ∧ (∀ (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E), orbU M f (actU g X) = orbU M f X) ∧ (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ a₀ : Inv r F, Delta a₀ ≠ 0 → ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀)) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a₀ : Inv r F) (X₀ : Hn r F E), Delta a₀ ≠ 0 → HasInv X₀ a₀ → ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  intro F E _ _ _ _ _ r M
  exact ⟨part1 F E r M, part2 F E r M, fun f' hf a₀ hΔ => part3 F E r M f' hf a₀ hΔ,
    fun f hf a₀ X₀ hΔ hX₀ => part4 F E r M f hf a₀ X₀ hΔ hX₀⟩

end GlobalTheory.JR.OrbLC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastMemConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
open Formalism.L2.Host (embLL0)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TwistProduct

variable {D : D7}

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (n : ℕ) (hn : 0 < n) :
    ChrEq (c ^ n) (χ ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [pow_succ, pow_succ]; exact GlobalTheory.TowerCharRead.chrEq_mul ih h

theorem chrEq_one_one : ChrEq (1 : (AE D)ˣ →* Circle) (1 : Formalism.L2.Host.HChar D.host.E) :=
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩

theorem natCast_mem_conj {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c, hc, e⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
  exact this ▸ hc

theorem tameAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ)
    (v : Pl D.host.E) : χ.TameAt v := by
  by_cases hv : v ∈ t.Q
  · have hr := GlobalTheory.TwistResidue.isRes_of_chrEq D t ht χ hχ v hv
    refine GlobalTheory.TameConjPlace.tameAt_of_congr χ v fun a b ka kb hka hkb ha hab => ?_
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    have hma : (Ideal.Quotient.mk v.asIdeal a : kP v) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
    have e1 := hr a ka (Units.mk0 _ hma) hka rfl
    have e2 := hr b kb (Units.mk0 _ hma) hkb (Ideal.Quotient.eq.mpr hab)
    rw [← e1, ← e2]
  · by_cases hc : ∃ P' ∈ t.Q, Formalism.IndefR.Lev.IsConjPl P' v
    · obtain ⟨P', hP', hPc⟩ := hc
      exact GlobalTheory.TameConjPlace.tameAt_conj D t ht χ hχ P' hP' v hPc
    · have hu := GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v hv hc
      intro x hx _
      exact hu x hx

theorem unrAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ) (pd : ℕ)
    (hpd : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (v : Pl D.host.E)
    (hv : ((pd : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) : χ.UnrAt v := by
  refine GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v (fun h => hv (hpd v h)) ?_
  rintro ⟨P', hP', hc⟩
  exact hv (natCast_mem_conj hc (hpd P' hP'))

theorem isTwist_mul : ∀ (D : D7) (t t' : Twist D Circle), t.Good → t'.Good → SplitSet (t.Q ∪ t'.Q) → Disjoint t.Q t'.Q →
    ∀ (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ), (∃ n : ℕ, 0 < n ∧ ∀ x, (t.chi * t'.chi) x ^ n = 1) →
    (∀ PP ∈ t.Q ∪ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, (((t.chi * t'.chi) x : Circle) : ℂ) ∈ σ.fieldRange) →
    ∃ δ : Formalism.L2.Host.HChar D.host.E, IsTwist pd σ δ (t.chi * t'.chi) := by
  intro D t t' ht ht' _ _ pd k _ σ hn hpd hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t.chi ht.isHeckeChar
  obtain ⟨χ', hχ'⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t'.chi ht'.isHeckeChar
  have hc : ChrEq (t.chi * t'.chi) (χ * χ') := GlobalTheory.TowerCharRead.chrEq_mul hχ hχ'
  have hpd1 : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_left _ h)
  have hpd2 : ∀ PP ∈ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_right _ h)
  refine ⟨χ * χ', hc, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn0, hnx⟩ := hn
    refine ⟨n, hn0, ?_⟩
    have hp := chrEq_pow hc n hn0
    have h1 : (t.chi * t'.chi) ^ n = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, hnx x, MonoidHom.one_apply]
    rw [h1] at hp
    exact GlobalTheory.ChrEqUnique.hchar_unique D 1 _ _ hp chrEq_one_one
  · exact GlobalTheory.T.heckeCharacter_trivialOnSubfield_of_idelicReading D _ _ hc fun a => by rw [MonoidHom.mul_apply, ht.real, ht'.real, one_mul]
  · intro v x hx hx1
    show χ.loc v x * χ'.loc v x = 1
    rw [tameAt_of_good t ht χ hχ v x hx hx1, tameAt_of_good t' ht' χ' hχ' v x hx hx1, one_mul]
  · intro v hv x hx
    show χ.loc v x * χ'.loc v x = 1
    rw [unrAt_of_good t ht χ hχ pd hpd1 v hv x hx, unrAt_of_good t' ht' χ' hχ' pd hpd2 v hv x hx, one_mul]
  · intro v _
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3 v
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (hval (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif v)))
    refine ⟨y, ?_⟩
    rw [hy, hc.2 v e he (Formalism.L2.Host.unif v) _ (Formalism.L2.JoinChr.locU_val hee _)]
    simp [Formalism.L2.Host.HChar.valTw, Formalism.L2.Host.HChar.val]

end GlobalTheory.TwistProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBallStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_tmul_mem_supLattice_of_mem_localUnitBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  first | exact @GlobalTheory.GeoTie.one_tmul_mem_Bsup | exact GlobalTheory.GeoTie.one_tmul_mem_Bsup | (intros; apply GlobalTheory.GeoTie.one_tmul_mem_Bsup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatchStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → CountIdentity := by
  first | exact @GlobalTheory.CountId.countIdentity_of_unitMatch | exact GlobalTheory.CountId.countIdentity_of_unitMatch | (intros; apply GlobalTheory.CountId.countIdentity_of_unitMatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPlacesDeclaredStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_places_declared : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, EmbeddingTypes.hypDecl i (X.dc i) ep ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) := by
  first | exact @GlobalTheory.NLink.splitPrime_hyps | exact GlobalTheory.NLink.splitPrime_hyps | (intros; apply GlobalTheory.NLink.splitPrime_hyps <;> assumption)
end

