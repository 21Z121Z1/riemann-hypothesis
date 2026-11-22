import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMap
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.ConstMu

theorem frobenius_ofPadic {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem frobenius_phiInv' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem frobenius_mu' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  conv_lhs => rw [← xi_mul_nu, map_mul, ← phiInv_mu, frobenius_phiInv']

theorem existsUnique_lattMap : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε g hg
  obtain ⟨ec, hec⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
  obtain ⟨em, hem⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
  have eig := GlobalTheory.T.existsUnique_padic_of_frobenius_eigen_ainf p C v O hv ε hε
  set l : latt (PDivGroup.mu p O) := em.symm 1 with hl_def
  have hl : l.1 (epsTate hε) = Sandwich.mu ε := by
    rw [← hem l, hl_def, LinearEquiv.apply_symm_apply, mul_one]
  have htate : ∀ t : (PDivGroup.mu p O).Tate, ∃ a : ℤ_[p], t = a • epsTate hε := by
    intro t
    obtain ⟨a, rfl⟩ := (epsEquiv hε).surjective t
    exact ⟨a, rfl⟩
  have hlval : ∀ a : ℤ_[p], l.1 (a • epsTate hε) = ofPadic p O a * Sandwich.mu ε := by
    intro a
    rw [map_smulₛₗ, hl, smul_eq_mul]
  have hgen : ∀ y : latt (PDivGroup.mu p O), y = em y • l := by
    intro y
    apply em.injective
    rw [map_smul, hl_def, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hpull : ∀ (f : const p O ⟶ PDivGroup.mu p O) (y : latt (PDivGroup.mu p O)),
      ec (lattMap f y) = y.1 (tateMap _ _ O f (constGen p O)) := by
    intro f y
    rw [hec]
    rfl

  set b : Ainf p O := ((g l).1 (constGen p O)) with hb_def
  have hbeig : WittVector.frobenius b = WittVector.frobenius (xi ε) * b := by
    have h1 := hg l (WittVector.frobenius (xi ε) • l) (by
      intro t
      obtain ⟨a, rfl⟩ := htate t
      rw [Submodule.coe_smul, LinearMap.smul_apply, hlval, smul_eq_mul, map_mul,
        frobenius_ofPadic, frobenius_mu']
      ring) (constGen p O)
    rw [map_smul, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hb_def, ← h1]
  obtain ⟨c, hc, hcu⟩ := eig b hbeig
  have hfix : ∀ f : const p O ⟶ PDivGroup.mu p O, lattMap f = g ↔
      ec (lattMap f l) = ec (g l) := by
    intro f
    constructor
    · intro h; rw [h]
    · intro h
      apply LinearMap.ext
      intro y
      rw [hgen y, map_smul, map_smul, ec.injective h]
  refine ⟨constHom (PDivGroup.mu p O) (c • epsTate hε), ?_, ?_⟩
  · show lattMap _ = g
    rw [hfix, hpull, tateMap_constHom, hlval, hec, hc]
  · intro f hf
    rw [hfix, hpull, hec] at hf
    obtain ⟨a, ha⟩ := htate (tateMap _ _ O f (constGen p O))
    rw [ha, hlval] at hf
    have hac : a = c := hcu a hf
    rw [← (constHom (PDivGroup.mu p O)).apply_symm_apply f, constHom_symm_apply, ha, hac]

end GlobalTheory.PDivLat.ConstMu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_basis_sections_abelianScheme_over_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  first | exact @GlobalTheory.exists_veryAmpleBy_basis_of_dvr | exact GlobalTheory.exists_veryAmpleBy_basis_of_dvr | (intros; apply GlobalTheory.exists_veryAmpleBy_basis_of_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetOfInvolutive
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.LKTorus

theorem cover_of_label {G : Type} [Group G] {ι : Type} (S : Finset ι) (T B : Subgroup G) (X : Set G)
    (lab : G → ι → Prop) (hlab : ∀ x ∈ X, x ∈ T → ∃ i ∈ S, lab x i)
    (hB : ∀ x y i, x ∈ X → y ∈ X → x ∈ T → y ∈ T → lab x i → lab y i → y⁻¹ * x ∈ B) :
    ∃ S' : Finset G, (∀ s ∈ S', s ∈ T) ∧ ∀ x ∈ X, x ∈ T → ∃ s ∈ S', s⁻¹ * x ∈ B ∧ s⁻¹ * x ∈ T := by
  classical
  let pick : ι → G := fun i => if h : ∃ y ∈ X, y ∈ T ∧ lab y i then h.choose else 1
  have hpick : ∀ i, (∃ y ∈ X, y ∈ T ∧ lab y i) → pick i ∈ X ∧ pick i ∈ T ∧ lab (pick i) i := by
    intro i h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  refine ⟨S.image pick, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    by_cases h : ∃ y ∈ X, y ∈ T ∧ lab y i
    · exact (hpick i h).2.1
    · simp only [pick, dif_neg h]; exact one_mem T
  · intro x hx hxT
    obtain ⟨i, hi, hl⟩ := hlab x hx hxT
    obtain ⟨h1, h2, h3⟩ := hpick i ⟨x, hx, hxT, hl⟩
    exact ⟨pick i, Finset.mem_image_of_mem _ hi, hB x (pick i) i hx h1 hxT h2 hl h3,
      mul_mem (inv_mem h2) hxT⟩

theorem finite_doubleCoset_of_involutive (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ x, c (c x) = x) :
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ U : Subgroup (simTA L c), IsOpen (U : Set (simTA L c)) →
      Finite (DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c))) := by
  letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  intro U hU
  classical

  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.1 hU
  have h1V : (1 : (AfE ℚ L)ˣ) ∈ V := by
    have h : (1 : simTA L c) ∈ (U : Set (simTA L c)) := one_mem U
    rw [← hVU] at h
    exact h
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.T.congruence_units_basis_of_nbhds L V hV h1V
  have hcongU : ∀ (x : (AfE ℚ L)ˣ) (hx : x ∈ simTA L c), x ∈ congN ℚ L N → (⟨x, hx⟩ : simTA L c) ∈ U := by
    intro x hx hxN
    have h : (⟨x, hx⟩ : simTA L c) ∈ Subtype.val ⁻¹' V := hNV x hxN
    rw [hVU] at h
    exact h

  obtain ⟨S₃, hS₃⟩ := GlobalTheory.T.ideles_finite_class_decomposition L
  let B1 : Subgroup (AfE ℚ L)ˣ := (ratId ℚ L).range ⊔ intU ℚ L
  obtain ⟨S₁, hS₁T, hS₁⟩ := cover_of_label S₃ (simTA L c) B1 Set.univ (fun x s => s⁻¹ * x ∈ B1)
    (fun x _ _ => by
      obtain ⟨s, hs, a, k, hk, rfl⟩ := hS₃ x
      refine ⟨s, hs, ?_⟩
      rw [mul_assoc, inv_mul_cancel_left]
      exact mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right hk))
    (fun x y s _ _ _ _ hx hy => by
      have e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x) := by group
      rw [e]
      exact mul_mem (inv_mem hy) hx)

  obtain ⟨S₆, hS₆⟩ := GlobalTheory.T.fixed_units_finitely_many_norms L c hc
  let B2 : Subgroup (AfE ℚ L)ˣ := (simT ℚ c).map (ratId ℚ L) ⊔ intU ℚ L
  let lab : (AfE ℚ L)ˣ → L → Prop := fun y f => ∃ (a : Lˣ) (k : (AfE ℚ L)ˣ) (r : ℚˣ) (η : Lˣ),
    k ∈ intU ℚ L ∧ IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ y = ratId ℚ L a * k ∧
      (a : L) * c a = algebraMap ℚ L r * (f * ((η : L) * c η))
  have hlab : ∀ y ∈ (B1 : Set (AfE ℚ L)ˣ), y ∈ simTA L c → ∃ f ∈ S₆, lab y f := by
    intro y hy hyT
    obtain ⟨z, ⟨a, rfl⟩, k, hk, rfl⟩ := Subgroup.mem_sup.1 hy
    obtain ⟨t, ht⟩ := hyT
    obtain ⟨r, u, hu1, hu2, rfl⟩ := GlobalTheory.T.rational_finite_idele_factorization t
    let ε : Lˣ := a * Units.map (c : L →+* L).toMonoidHom a * (Units.map (algebraMap ℚ L).toMonoidHom r)⁻¹
    have key : ratId ℚ L ε = idF ℚ L u * (k * conjId c k)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      have e1 : ratId ℚ L ε * (k * conjId c k) =
          (ratId ℚ L a * k * conjId c (ratId ℚ L a * k)) * (ratId ℚ L (Units.map (algebraMap ℚ L).toMonoidHom r))⁻¹ := by
        simp only [ε, map_mul, map_inv, conjId_ratId]
        simp only [mul_comm, mul_left_comm, mul_assoc]
      rw [e1, ht, map_mul, idF_map_algebraMap, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have hεU : ratId ℚ L ε ∈ intU ℚ L := by
      rw [key]
      exact mul_mem (idF_mem_intU L hu1 hu2) (inv_mem (mul_mem hk (conjId_mem_intU L c hk)))
    obtain ⟨hε1, hε2⟩ := (GlobalTheory.T.principal_idele_integral_iff_unit L ε).1 hεU
    have hεc : c (ε : L) = ε := by
      simp only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
        RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_inv₀, hc,
        AlgHom.commutes]
      ring
    obtain ⟨f, hf, η, hη1, hη2, hεf⟩ := hS₆ ε hε1 hε2 hεc
    refine ⟨f, hf, a, k, r, η, hk, hη1, hη2, rfl, ?_⟩
    rw [← hεf]
    have hr : algebraMap ℚ L (r : ℚ) ≠ 0 := by simp
    simp only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp

  have hB : ∀ x y f, x ∈ (B1 : Set (AfE ℚ L)ˣ) → y ∈ (B1 : Set (AfE ℚ L)ˣ) → x ∈ simTA L c → y ∈ simTA L c →
      lab x f → lab y f → y⁻¹ * x ∈ B2 := by
    rintro x y f - - - - ⟨a, k, r, η, hk, hη1, hη2, rfl, ha⟩ ⟨a', k', r', η', hk', hη1', hη2', rfl, ha'⟩
    have hf : f ≠ 0 := by
      rintro rfl
      rw [zero_mul, mul_zero] at ha
      exact mul_ne_zero a.ne_zero ((map_ne_zero c).2 a.ne_zero) ha
    let b : Lˣ := a * a'⁻¹ * η' * η⁻¹
    have hb : b ∈ simT ℚ c := by
      refine ⟨r * r'⁻¹, ?_⟩
      have hη0 : (η : L) * c η ≠ 0 := mul_ne_zero η.ne_zero ((map_ne_zero c).2 η.ne_zero)
      have hη0' : (η' : L) * c η' ≠ 0 := mul_ne_zero η'.ne_zero ((map_ne_zero c).2 η'.ne_zero)
      have hr' : algebraMap ℚ L (r' : ℚ) ≠ 0 := by simp
      have e : (b : L) * c b = ((a : L) * c a) * ((a' : L) * c a')⁻¹ * ((η' : L) * c η') * ((η : L) * c η)⁻¹ := by
        simp only [b, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
        ring
      rw [e, ha, ha']
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
      field_simp
    have hab : a = b * (η * η'⁻¹) * a' := by
      apply Units.ext
      simp only [b, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    have hint : ratId ℚ L (η * η'⁻¹) ∈ intU ℚ L := by
      rw [GlobalTheory.T.principal_idele_integral_iff_unit]
      constructor
      · simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hη2' ⊢
        exact hη1.mul hη2'
      · simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hη2 ⊢
        exact hη1'.mul hη2
    have e2 : (ratId ℚ L a' * k')⁻¹ * (ratId ℚ L a * k) = ratId ℚ L b * (ratId ℚ L (η * η'⁻¹) * (k'⁻¹ * k)) := by
      rw [hab, map_mul, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e2]
    exact mul_mem (Subgroup.mem_sup_left ⟨b, hb, rfl⟩)
      (Subgroup.mem_sup_right (mul_mem hint (mul_mem (inv_mem hk') hk)))
  obtain ⟨S₂, hS₂T, hS₂⟩ := cover_of_label S₆ (simTA L c) B2 (B1 : Set (AfE ℚ L)ˣ) lab hlab hB

  obtain ⟨S₄, hS₄⟩ := GlobalTheory.T.integral_units_finite_cosets L N hN
  obtain ⟨S₅, hS₅T, hS₅⟩ := cover_of_label S₄ (simTA L c) (congN ℚ L N) (intU ℚ L : Set (AfE ℚ L)ˣ)
    (fun k s => s⁻¹ * k ∈ congN ℚ L N) (fun k hk _ => hS₄ k hk)
    (fun x y s _ _ _ _ hx hy => by
      have e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x) := by group
      rw [e]
      exact mul_mem (inv_mem hy) hx)

  let rep : (S₁ × S₂ × S₅) → DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c)) :=
    fun p => DoubleCoset.mk (ratT L c) U ⟨p.1.1 * p.2.1.1 * p.2.2.1,
      mul_mem (mul_mem (hS₁T _ p.1.2) (hS₂T _ p.2.1.2)) (hS₅T _ p.2.2.2)⟩
  refine Finite.of_surjective rep ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h x =>
  obtain ⟨x, hxT⟩ := x
  obtain ⟨s₁, hs₁, hy1, hyT⟩ := hS₁ x (Set.mem_univ _) hxT
  obtain ⟨s₂, hs₂, hz2, hzT⟩ := hS₂ _ hy1 hyT
  obtain ⟨γ, ⟨b, hb, rfl⟩, k, hk, hγk⟩ := Subgroup.mem_sup.1 hz2
  have hγT : ratId ℚ L b ∈ simTA L c := ratId_mem_simTA L c hb
  have hkT : k ∈ simTA L c := by
    have e : k = (ratId ℚ L b)⁻¹ * (s₂⁻¹ * (s₁⁻¹ * x)) := by rw [← hγk, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hγT) hzT
  obtain ⟨s₅, hs₅, hw, hwT⟩ := hS₅ k hk hkT
  refine ⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ⟨s₅, hs₅⟩), ?_⟩
  show DoubleCoset.mk (ratT L c) U _ = DoubleCoset.mk (ratT L c) U _
  rw [DoubleCoset.eq]
  refine ⟨⟨ratId ℚ L b, hγT⟩, (Subgroup.mem_subgroupOf).2 ⟨b, hb, rfl⟩, ⟨s₅⁻¹ * k, hwT⟩, hcongU _ hwT hw, ?_⟩
  apply Subtype.ext
  have hx : x = s₁ * (s₂ * (ratId ℚ L b * k)) := by
    rw [hγk]
    group
  simp only [Subgroup.coe_mul]
  rw [hx]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem finite_doubleCoset (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ (τ : L →+* ℂ) (x : L), τ (c x) = (starRingEnd ℂ) (τ x)) :
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ U : Subgroup (simTA L c), IsOpen (U : Set (simTA L c)) →
      Finite (DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c))) := by
  have hinv : ∀ x, c (c x) = x := by
    let τ : L →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := L)).toRingHom
    intro x
    apply τ.injective
    rw [hc, hc, Complex.conj_conj]
  exact finite_doubleCoset_of_involutive L c hinv

end GlobalTheory.LKTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW

theorem psiLoc_addChar_locallyConstant_ne_one :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ,
      (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  intro E _ _ w
  refine ⟨psiLocChar w, fun x => rfl, ?_, ?_⟩
  · have hc : Continuous (psiLocChar w) := by
      have : (psiLocChar w : w.adicCompletion E → ℂ) = fun x => ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) := by
        funext x; exact GlobalTheory.JSW.WhitModel.psiLoc_eq w x
      rw [this]
      exact continuous_subtype_val.comp (GroundTheory.Global.continuous_localAdelicChar w)
    exact GlobalTheory.SchrSBFin.isLocallyConstant_addChar _ hc
  · intro h
    apply GroundTheory.Global.localAdelicChar_ne_one (K := E) (v := w)
    refine AddChar.ext _ _ fun x => ?_
    have h1 : psiLocChar w x = 1 := by rw [h]; rfl
    have h2 : ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) = 1 := by
      rw [← GlobalTheory.JSW.WhitModel.psiLoc_eq]; exact h1
    exact Subtype.ext h2

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatProductDepthPeriodicGcd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem gcd_nsmul_mem_of {A S : Type*} [AddCommGroup A] [SetLike S A] [AddSubgroupClass S A] (Λ : S) {x : A}
    {k k' : ℕ} (h : k • x ∈ Λ) (h' : k' • x ∈ Λ) : Nat.gcd k k' • x ∈ Λ := by
  have e : Nat.gcd k k' • x = Nat.gcdA k k' • (k • x) + Nat.gcdB k k' • (k' • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, Nat.gcd_eq_gcd_ab]
    congr 1; ring
  rw [e]
  exact add_mem (zsmul_mem h _) (zsmul_mem h' _)

theorem add_mul_succ_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    z + ((k : ℤ) * (n + 1)) • w = (z + ((k : ℤ) * n) • w) + k • w := by
  rw [mul_add, mul_one, add_smul, natCast_zsmul, add_assoc]

theorem add_mul_pred_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    (z + ((k : ℤ) * (n - 1)) • w) + k • w = z + ((k : ℤ) * n) • w := by
  rw [add_assoc, ← natCast_zsmul, ← add_smul]; congr 2; ring

theorem add_gcd_nsmul_eq {A : Type*} [AddCommGroup A] (k k' : ℕ) (z w : A) :
    z + Nat.gcd k k' • w = (z + ((k : ℤ) * Nat.gcdA k k') • w) + ((k' : ℤ) * Nat.gcdB k k') • w := by
  rw [add_assoc, ← add_smul, ← Nat.gcd_eq_gcd_ab, natCast_zsmul]

theorem isHalf_add_zsmul {e : AE D} {m n : ℕ} {a b : Mx D m n} (ha : IsHalf e a) (hb : IsHalf e b) (c : ℤ) :
    IsHalf e (a + c • b) := fun i j => by
  have h1 := ha i j
  have h2 := hb i j
  show e * (a i j + c • b i j) = a i j + c • b i j
  rw [zsmul_eq_mul, mul_add, mul_left_comm, h1, h2]

theorem DepthOK.flatProd_add_zsmul {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t} {e : AE D} {k : ℕ}
    (hK : DepthOK S t Φ β e k) (c : ℤ)
    (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))
    (hx : ∀ j, IsHalf e (x j)) (hy : ∀ i, IsHalf e (y i))
    (hu : ∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j))
    (hv : ∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) :
    flatProd S t Φ β (x + ((k : ℤ) * c) • u) (y + ((k : ℤ) * c) • v) = flatProd S t Φ β x y := by
  induction c using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [add_mul_succ_zsmul, add_mul_succ_zsmul,
      hK.2 (x + ((k : ℤ) * n) • u) u (y + ((k : ℤ) * n) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv, ih]
  | pred n ih =>
    rw [← hK.2 (x + ((k : ℤ) * (-n - 1)) • u) u (y + ((k : ℤ) * (-n - 1)) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
      add_mul_pred_zsmul, add_mul_pred_zsmul, ih]

theorem depthOK_gcd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ)
    (h : DepthOK S t Φ β e k) (h' : DepthOK S t Φ β e k') : DepthOK S t Φ β e (Nat.gcd k k') := by
  refine ⟨fun x y hx hy hF => ⟨fun j => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).1 j) ((h'.1 x y hx hy hF).1 j),
    fun i => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).2 i) ((h'.1 x y hx hy hF).2 i)⟩, ?_⟩
  intro x u y v hx hy hu hv
  rw [add_gcd_nsmul_eq k k' x u, add_gcd_nsmul_eq k k' y v,
    h'.flatProd_add_zsmul _ (x + ((k : ℤ) * Nat.gcdA k k') • u) u (y + ((k : ℤ) * Nat.gcdA k k') • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _)
      (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
    h.flatProd_add_zsmul _ x u y v hx hy hu hv]

end GlobalTheory.DepthUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBoundedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_vanishes_unless_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  first | exact @GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded | exact GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded | (intros; apply GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipAtEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareFlipReach

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def rowE (t : T) (w : Pl D.host.E) (i j : Fin D.R.m) :
    Fin ((locGrid G t w).rank (i + 1, j + 1)) ≃ Fin (spW G i j).rank :=
  finCongr (rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨i.2, j.2⟩)

def colE (t : T) (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) :
    (locGrid G t w).Cols i j ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank) :=
  (Equiv.sumCongr (finCongr (rank_vertex G t w (X := ((i : ℕ), (j : ℕ) + 1)) ⟨i.2.le, j.2⟩))
    (finCongr (rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ))) ⟨i.2, j.2.le⟩))).trans e

def trA (t : T) {w : Pl D.host.E} {v : Pl D.host.F} (hv : w.under (𝓞 D.host.F) = v) {i j : Fin D.R.m} (e : Num G i j)
    (Z : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) :=
  Matrix.of fun r c => GlobalTheory.LFun.complMap hv (Z (rowE t w i j r) (colE t w e c))

def sqCore (W : G.Weil) (t : T) (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  phiA (haarVol ((givenLevel G t w (i, j)).map invT)) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _))
    (fourierSum (psiAt W w) (unifAt w) n (Assignment.one.block _ _) Φ)

theorem flipAt_eq (W : G.Weil) (t : T) (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    flipAt W t i j w n Φ = invFourierSum (psiAt W w)⁻¹ (unifAt w) n (Assignment.one.block _ _)ᶜ (sqCore W t i j w n Φ) := rfl

end GlobalTheory.SquareFlipReach

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsOriginOppositeSignVacuumConjPeriodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJets_origin_oppositeSignVacuum_conjPeriod : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FunObj.FockChi.fockIn_chi_zero | exact GlobalTheory.FunObj.FockChi.fockIn_chi_zero | (intros; apply GlobalTheory.FunObj.FockChi.fockIn_chi_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlaceStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    Set.BijOn (fun (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) => ∫ x, φ x * ψ (x ⬝ᵥ y) ∂μ)
      (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := by
  first | exact @GlobalTheory.FourierLocBij.fourier_bijOn | exact GlobalTheory.FourierLocBij.fourier_bijOn | (intros; apply GlobalTheory.FourierLocBij.fourier_bijOn <;> assumption)
end

