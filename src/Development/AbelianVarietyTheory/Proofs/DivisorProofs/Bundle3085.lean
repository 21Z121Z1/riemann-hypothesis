import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariable
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.Poincare

theorem eq_zero_of_algebraMap_mem_rel {R G : Type} [CommRing R] [CommRing G] [Algebra R G] {J' : Ideal G}
    (δ' : DividedPowers J') (g : G) (hg : algebraMap G (DR R G) g ∈ rel R δ') : g = 0 := by
  have hle : rel R δ' ≤ RingHom.ker (ExteriorAlgebra.algebraMapInv (R := G) (M := Ω[G⁄R])).toRingHom := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨m, a, _, rfl⟩
    simp [ExteriorAlgebra.algebraMapInv]
  have := hle hg
  rw [RingHom.mem_ker] at this
  simpa [ExteriorAlgebra.algebraMap_leftInverse _ g] using this

theorem mDR_mDR {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
    {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}
    (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ) (e : ∀ b, β (α b) = γ b) (x : DR R B) :
    h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.PDForm.Poincare

open GlobalTheory.PDForm.Poincare in

theorem GlobalTheory.PDForm.rq_truncPoly : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  intro R B _ _ _ J δ Q _ _ η G _ _ J' δ' q n hstd hlev hq hqd hqs hJ' hker α h hd hα

  obtain ⟨ε, hεs, hεd, hεb, hεe⟩ : ∃ ε : Q.P →+* B, SemiHom (RingHom.id R) ε ∧ IsDPMorphism η δ ε ∧
      (∀ b, ε (algebraMap B Q.P b) = b) ∧ ∀ k, ε (Q.e (k + 1)) = 0 := by
    obtain ⟨ε0, hε0⟩ := (GlobalTheory.PDA.PDPoly.exists_lift_and_aug B Q).2
    have hb : ∀ b, ε0 (algebraMap B Q.P b) = b := fun b ↦ ε0.commutes b
    refine ⟨ε0, fun r p ↦ ?_, ?_, hb, fun k ↦ (hε0 _).1 (Q.e_succ_mem_aug k)⟩
    · change ε0 (r • p) = r • ε0 p
      rw [← algebraMap_smul B r p, map_smul, algebraMap_smul]
    · refine GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd B J δ Q η hstd B J δ ε0 0 J.zero_mem ⟨?_, ?_⟩ ?_
      · intro x hx
        rw [Ideal.mem_map_iff_of_surjective _ (fun b ↦ ⟨b, hb b⟩)] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa [hb] using hy
      · intro k a _
        simp [hb]
      · intro k
        cases k with
        | zero => change ε0 (Q.e 0) = _; rw [Q.e_zero, map_one, δ.dpow_zero J.zero_mem]
        | succ k => change ε0 (Q.e (k + 1)) = _; rw [(hε0 _).1 (Q.e_succ_mem_aug k), δ.dpow_eval_zero (Nat.succ_ne_zero k)]
  have hi : SemiHom (RingHom.id R) (algebraMap B Q.P) := fun r b ↦ map_smul (IsScalarTower.toAlgHom R B Q.P) r b

  have hkε : ∀ p, q p = 0 → ε p = 0 := by
    intro p hp
    have h1 : ε p ∈ fil δ (n + 1) :=
      (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.2.2 B J δ ε hεd (n + 1) (Ideal.mem_map_of_mem _ ((hker p).1 hp))
    rw [hlev] at h1
    exact (Ideal.mem_bot).1 h1
  obtain ⟨eb, hebq⟩ : ∃ eb : G →+* B, ∀ p, eb (q p) = ε p :=
    ⟨q.liftOfRightInverse (Function.surjInv hqs) (Function.rightInverse_surjInv hqs) ⟨ε, fun p hp ↦ hkε p hp⟩,
      fun p ↦ RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  have hebα : ∀ b, eb (α b) = b := fun b ↦ by rw [hα, hebq, hεb]
  have heb : SemiHom (RingHom.id R) eb := by
    intro r g
    obtain ⟨p, rfl⟩ := hqs g
    have := hq r p
    simp only [RingHom.id_apply] at this ⊢
    rw [← this, hebq, hebq]
    simpa using hεs r p
  have hdeb : IsDPMorphism δ' δ eb := by
    have hc : eb.comp q = ε := RingHom.ext hebq
    refine ⟨?_, ?_⟩
    · rw [hJ', Ideal.map_map, hc]; exact hεd.1
    · intro k a ha
      rw [hJ', Ideal.mem_map_iff_of_surjective _ hqs] at ha
      obtain ⟨a, ha, rfl⟩ := ha
      rw [hebq, hqd.2 a ha, hebq, hεd.2 a ha]
  have hid : SemiHom (RingHom.id R) (RingHom.id B) := fun _ _ ↦ rfl
  have hdid : IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism
  have ret1 : ∀ x, km1 heb hdeb (km1 h hd x) = x := fun x ↦
    (divPowerCompatOneFormMap_comp h hd heb hdeb hid hdid hebα x).trans (divPowerCompatOneFormMap_id hid hdid (fun _ ↦ rfl) x)
  have ret : ∀ j x, km heb hdeb j (km h hd j x) = x := fun j x ↦
    (km_km h hd heb hdeb hid hdid hebα j x).trans (km_id hid hdid (fun _ ↦ rfl) j x)

  obtain ⟨v, hv0, hv1, hv2⟩ := GlobalTheory.PDA.PDPoly.exists_der R B J δ Q η hstd
  have he : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    rw [← hstd.var k]
    exact (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k _ (Q.e_one_mem_ext J)
  have hht := GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e (n + 1) hv2 he
  have kq := GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms R Q.P (Q.ext J) η G J' δ' q hq n hqd hqs hJ' hker
  have kdr := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R Q.P G q hq hqs
  have key : ∀ X : DR R Q.P, hq.mDR (dDR R Q.P X) ∈ rel R δ' →
      hq.mDR X - h.mDR (hεs.mDR X) - dDR R G (hq.mDR (hot v Q.e (n + 1) X)) ∈ rel R δ' := by
    intro X hX
    have hT := hht.2.2.2.2 n _ (kq.1 _ hX)
    have hH := GlobalTheory.T.dividedPowerPolyAlgebra_homotopy_identity R B J δ Q η v hi hstd hv0 hv1 hv2 ε hεs hεd hεb hεe (n + 1) X
    have h3 := add_mem hH hT
    rw [sub_add_cancel] at h3
    have := kq.2 _ h3
    rwa [map_sub, map_sub, mDR_mDR hi hq h (fun b ↦ (hα b).symm), hq.mDR_dDR] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x _ hx
    have hx' : α x = 0 := hx
    rw [← hebα x, hx', map_zero]
  ·
    intro y hy
    obtain ⟨p, rfl⟩ := hqs y
    have hy' : hq.mDR (dDR R Q.P (algebraMap Q.P (DR R Q.P) p)) ∈ rel R δ' := by
      rw [dDR_algebraMap, hq.mDR_ι, hq.m1_D]
      exact (Submodule.Quotient.mk_eq_zero (N1 R δ')).1 (by rw [← divPowerCompatFunctionDifferential_apply]; exact hy)
    have hk := key _ hy'
    rw [(hht.2.1 p), map_zero, map_zero, sub_zero, hq.mDR_algebraMap, hεs.mDR_algebraMap, h.mDR_algebraMap,
      ← map_sub] at hk
    have hp : q p = α (ε p) := sub_eq_zero.1 (eq_zero_of_algebraMap_mem_rel δ' _ hk)
    refine ⟨ε p, ?_, hp.symm⟩
    have h0 : km1 h hd (kd0 R δ (ε p)) = 0 := by rw [divPowerCompatOneFormMap_functionDifferential, ← hp]; exact hy
    rw [← ret1 (kd0 R δ (ε p)), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨eb y, ?_⟩
    rw [← divPowerCompatOneFormMap_functionDifferential heb hdeb, ← hxy, ret1]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.1 y
    have hy' : hq.mDR (dDR R Q.P (ι1 ω)) ∈ rel R δ' := by
      rw [hq.mDR_dDR, hq.mDR_ι]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 2)).1 (by rw [← divPowerCompatOneFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, algebraMap Q.P (DR R Q.P) c = hot v Q.e (n + 1) (ι1 ω) := by
      have := hht.2.2.1 0 _ (ι_mem ω)
      change _ ∈ LinearMap.range _ ^ 0 at this
      rwa [pow_zero, Submodule.mem_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_algebraMap, dDR_algebraMap, hq.mDR_ι, hεs.mDR_ι, h.mDR_ι, ← map_sub, ← map_sub] at hk
    set x : K1 R δ := Submodule.Quotient.mk (hεs.m1 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.m1 ω) : K1 R δ') = km1 h hd x + kd0 R δ' (q c) := by
      rw [divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, q c, ?_, heq⟩
    have h0 : km h hd 2 (kd1 R δ x) = 0 := by
      rw [divPowerCompatFormMap_oneFormDerivative, show km1 h hd x = Submodule.Quotient.mk (hq.m1 ω) - kd0 R δ' (q c) by rw [heq]; abel,
        map_sub, divPowerCompatOneFormDerivative_comp_differential, sub_zero]
      exact hy
    rw [← ret 2 (kd1 R δ x), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨km1 heb hdeb y, ?_⟩
    rw [← divPowerCompatFormMap_oneFormDerivative heb hdeb, ← hxy, ret]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.2.1 2 y
    have hy' : hq.mDR (dDR R Q.P (ω : DR R Q.P)) ∈ rel R δ' := by
      rw [hq.mDR_dDR]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 3)).1 (by rw [← divPowerCompatTwoFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, ι1 c = hot v Q.e (n + 1) (ω : DR R Q.P) := by
      have := hht.2.2.1 1 _ ω.2
      change _ ∈ LinearMap.range _ ^ 1 at this
      rwa [pow_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_ι] at hk
    set x : K R δ 2 := Submodule.Quotient.mk (hεs.mOm 2 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.mOm 2 ω) : K R δ' 2) = km h hd 2 x + kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) := by
      rw [km_mk, divPowerCompatOneFormDerivative_mk, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, Submodule.Quotient.mk (hq.m1 c), ?_, heq⟩
    have h0 : km h hd 3 (kd2 R δ x) = 0 := by
      rw [divPowerCompatFormMap_twoFormDerivative, show km h hd 2 x = Submodule.Quotient.mk (hq.mOm 2 ω) - kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) by
        rw [heq]; abel, map_sub, divPowerCompatTwoFormDerivative_comp_oneForm, sub_zero]
      exact hy
    rw [← ret 3 (kd2 R δ x), h0, map_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.DimDeg

def DimFormula (R : Type) [CommRing R] (c : ℕ) : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B] [Algebra.FiniteType R B] (e : ℕ),
    Algebra.trdeg R B = e → ringKrullDim B = (e + c : ℕ)

theorem dimFormula_field (F : Type) [Field F] : DimFormula F 0 := by
  intro B _ _ _ _ _ e he
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F B
  have : d = e := by exact_mod_cast h₂.symm.trans he
  rw [h₁, this, add_zero]

theorem dimFormula_int : DimFormula ℤ 1 := by
  intro B _ _ _ _ _ e he
  have : CharZero B := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ B)
  refine le_antisymm ?_ (PrimeDivDim.succ_trdeg_le_ringKrullDim B he)
  have hZ1 : ringKrullDim ℤ ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
  rw [ringKrullDim_genericFibre_eq ℤ ℚ he]
  refine (add_le_add hZ1 (le_refl ((e : ℕ) : WithBot ℕ∞))).trans_eq ?_
  push_cast
  exact add_comm _ _

theorem exists_dim_quotient_ker {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {A K : Type} [CommRing A] (hA : (Int.castRingHom A).FiniteType)
    [Field K] [Algebra R K] [FaithfulSMul R K] (φ : A →+* K) (hφ : ∀ z : K, ∃ a b : A, z = φ a / φ b) :
    ∃ e : ℕ, Algebra.trdeg R K = e ∧ ringKrullDim (A ⧸ RingHom.ker φ) = (e + c : ℕ) := by
  let B : Subalgebra R K :=
    { φ.range.toSubsemiring with
      algebraMap_mem' := fun r => by
        obtain ⟨n, rfl⟩ := hs r
        exact ⟨n, by simp⟩ }
  let ψ : A →+* B := φ.codRestrict B fun a => ⟨a, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hft : Algebra.FiniteType R B := by
    have h1 : (ψ.comp (Int.castRingHom A)).FiniteType := (RingHom.FiniteType.of_surjective ψ hψ).comp hA
    rw [Subsingleton.elim (ψ.comp (Int.castRingHom A)) ((algebraMap R B).comp (Int.castRingHom R))] at h1
    exact RingHom.finiteType_algebraMap.1 h1.of_comp_finiteType
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    FaithfulSMul.algebraMap_injective R K (by
      rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K, h])
  have : IsFractionRing B K := IsFractionRing.of_field B K fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨ψ a, ψ b, h⟩
  have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast R (A := B)
  refine ⟨e, (trdeg_eq_of_isAlgebraic_top R B K).trans he, ?_⟩
  have hk : RingHom.ker φ = RingHom.ker ψ := Ideal.ext fun a => by
    simp only [RingHom.mem_ker]
    exact (Subtype.ext_iff (a1 := ψ a) (a2 := 0)).symm
  rw [← hR B e he, hk]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ)

theorem exists_dim_inter {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧
      topologicalKrullDim ((U : Set X) ∩ closure {x} : Set X) = (e + c : ℕ) := by
  have hA : (Int.castRingHom Γ(X, U)).FiniteType := by
    let φ := Spec.preimage (hU.fromSpec ≫ t)
    have hφ : Spec.map φ = hU.fromSpec ≫ t := Spec.map_preimage _
    have h := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
    rwa [Subsingleton.elim (Int.castRingHom Γ(X, U)) φ.hom]
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨e, h₁, h₂⟩ := exists_dim_quotient_ker hR hs hA (X.evaluation U x hx).hom (by
    intro z
    obtain ⟨w, rfl⟩ := X.residue_surjective x z
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (S := X.presheaf.stalk x) w
    have hu := (IsLocalization.map_units (X.presheaf.stalk x) b).map (X.residue x).hom
    refine ⟨a, b, (eq_div_iff hu.ne_zero).2 ?_⟩
    exact (map_mul (X.residue x).hom _ _).symm.trans (congrArg (X.residue x).hom h))
  refine ⟨e, h₁, ?_⟩
  have hk : RingHom.ker (X.evaluation U x hx).hom = (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    ext f
    rw [RingHom.mem_ker]
    refine (X.evaluation_eq_zero_iff_notMem_basicOpen x hx f).trans ?_
    have h := hU.fromSpec_preimage_basicOpen f
    have h' : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
      SetLike.ext_iff.1 h (hU.primeIdealOf ⟨x, hx⟩)
    rw [hU.fromSpec_primeIdealOf] at h'
    exact h'.not.trans not_not
  have h := topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)
  rw [← h₂, hk, ← h]
  have h3 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h4 := hU.range_fromSpec
  exact congrArg (fun s : Set X => topologicalKrullDim s)
    (congrArg₂ (· ∩ ·) h4.symm (congrArg (fun z => closure {z}) h3.symm))

theorem exists_hasDim {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧ HasDim x (e + c) := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
  obtain ⟨e, h₁, h₂⟩ := exists_dim_inter hR hs t x hU hxU
  refine ⟨e, h₁, le_antisymm ?_ ?_⟩
  · refine topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_
    obtain ⟨V, hV, hzV, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top z.1)
    have hxV : x ∈ V := (specializes_iff_mem_closure.2 z.2).mem_open V.isOpen hzV
    obtain ⟨e', h₁', h₂'⟩ := exists_dim_inter hR hs t x hV hxV
    obtain rfl : e = e' := by exact_mod_cast h₁.symm.trans h₁'
    refine ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val, hzV, ?_⟩
    rw [← h₂']
    refine (topologicalKrullDim_eq_of_isEmbedding
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal) ?_).ge
    rw [Set.range_comp, Subtype.range_val, Subtype.image_preimage_val, Set.inter_comm]
  · rw [← h₂]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le

theorem locallyOfFiniteType_of_isAmb {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (h : IsAmb p) :
    LocallyOfFiniteType p := by
  obtain ⟨N, jN, _, hjN⟩ := h.isProjOver
  have := isProper_str k N
  have : IsProper p := hjN ▸ inferInstance
  infer_instance

theorem le_and_iff_of_dimFormula {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X Y : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t]
    (π : Y ⟶ X) [LocallyOfFiniteType π] (y : Y) [Algebra R (X.residueField (π y))]
    [FaithfulSMul R (X.residueField (π y))] (d d' : ℕ) (hd : HasDim y d) (hd' : HasDim (π y) d') :
    d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  letI := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra R (Y.residueField y) := ((π.residueFieldMap y).hom.comp (algebraMap R _)).toAlgebra
  haveI : IsScalarTower R (X.residueField (π y)) (Y.residueField y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul R (Y.residueField y) := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((π.residueFieldMap y).hom.injective.comp (FaithfulSMul.algebraMap_injective R _))
  haveI : Algebra.EssFiniteType (X.residueField (π y)) (Y.residueField y) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap π y)
  obtain ⟨e, h₁, h₂⟩ := exists_hasDim hR hs (π ≫ t) y
  obtain ⟨e', h₁', h₂'⟩ := exists_hasDim hR hs t (π y)
  obtain rfl : d = e + c := by exact_mod_cast hd.symm.trans h₂
  obtain rfl : d' = e' + c := by exact_mod_cast hd'.symm.trans h₂'
  have hadd := trdeg_add_eq R (X.residueField (π y)) (A := Y.residueField y)
  rw [h₁, h₁'] at hadd
  have hle : e' ≤ e := by exact_mod_cast (self_le_add_right _ _).trans_eq hadd
  refine ⟨by omega, ?_⟩
  change Module.finrank (X.residueField (π y)) (Y.residueField y) ≠ 0 ↔ _
  constructor
  · intro h
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
    rw [trdeg_eq_zero, add_zero] at hadd
    have : e' = e := by exact_mod_cast hadd
    rw [this]
  · intro h
    obtain rfl : e = e' := by omega
    have h0 : Algebra.trdeg (X.residueField (π y)) (Y.residueField y) = 0 := by
      rcases (Cardinal.add_eq_left_iff).1 hadd with h | h
      · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 Cardinal.natCast_lt_aleph0)
      · exact h
    have : Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y) := trdeg_eq_zero_iff.1 h0
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact Module.finrank_pos.ne'

theorem dim_le_and_residueDegree_ne_zero_iff : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (π : Y ⟶ X), π ≫ p = q → ∀ (y : Y) (d d' : ℕ), HasDim y d → HasDim (π y) d' → d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  intro k _ X Y p q hp hq π hπ y d d' hd hd'
  have := locallyOfFiniteType_of_isAmb hp
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ locallyOfFiniteType_of_isAmb hq
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hp.finite)
  obtain ⟨l, hl⟩ := CharP.exists (X.residueField (π y))
  rcases CharP.char_is_prime_or_zero (X.residueField (π y)) l with h | rfl
  · haveI : Fact l.Prime := ⟨h⟩
    letI := ZMod.algebra (X.residueField (π y)) l
    exact le_and_iff_of_dimFormula (dimFormula_field (ZMod l)) (ZMod.intCast_surjective)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'
  · haveI := CharP.charP_to_charZero (X.residueField (π y))
    exact le_and_iff_of_dimFormula dimFormula_int (fun n => ⟨n, rfl⟩)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'

end GlobalTheory.DimDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationKernelKilledOverDvrOfGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerExt

theorem kernel_killed : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) → ∀ m : ℕ, (∀ (T : Over (Sp L)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ m = 1) → ∀ (T : Over (Sp W)) (x : T ⟶ G), (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ m = 1 := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hab hpb hsq P P' hP hP' hPP' h1 h2 hsym hamp m hA T x hx
  obtain ⟨H, i, -, -, hflat, hker⟩ := GlobalTheory.T.finiteFlat_kernel_symmetric_birigidified_bundle W G hab P' hP' h1 h2 hsym hamp
  obtain ⟨y, rfl⟩ := (hker T x).1 hx
  have key : i ^ m = 1 := by
    haveI := hab.proper
    haveI : IsOpenImmersion (spMap (algebraMap W L)) := isOpenImmersion_spMap_of_isDiscreteValuationRing W L
    haveI : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
    refine GrpDense.hom_ext_of_points (spMap (algebraMap W L)) (fun T' t => ?_)
    obtain ⟨z, hz⟩ := GrpDense.pushPt_surjective hpb.1 T' (t ≫ i)
    have hzl : z.left ≫ φ = t.left ≫ i.left := congrArg (fun q => q.left) hz
    let F := (lift (snd G H ≫ i) (fst G H)).left
    obtain ⟨s, hs⟩ : ∃ s : (P'.pull F).Gen, s.IsGen := (hker H i).2 ⟨𝟙 H, Category.id_comp _⟩
    let c := (lift (snd A T' ≫ z) (fst A T')).left
    let q : Over.mk ((A ⊗ T').hom ≫ spMap (algebraMap W L)) ⟶ H :=
      Over.homMk ((snd A T').left ≫ t.left) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [Over.w t]
        show (snd A T').left ≫ T'.hom ≫ _ = _
        rw [← Category.assoc, Over.w (snd A T')])
    let Ψ := (lift (pushPt hpb.1.w (fst A T')) q).left
    have hΨ1 : Ψ ≫ (fst G H).left = (fst A T').left ≫ φ := by rw [← Over.comp_left, lift_fst]; rfl
    have hΨ2 : Ψ ≫ (snd G H).left = (snd A T').left ≫ t.left := by rw [← Over.comp_left, lift_snd]; rfl
    have hF1 : F ≫ (fst G G).left = (snd G H).left ≫ i.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
    have hF2 : F ≫ (snd G G).left = (fst G H).left := by rw [← Over.comp_left, lift_snd]
    have hc1 : c ≫ (fst A A).left = (snd A T').left ≫ z.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
    have hc2 : c ≫ (snd A A).left = (fst A T').left := by rw [← Over.comp_left, lift_snd]
    have hc : Ψ ≫ F = c ≫ φ₂ := by
      apply Over.tensorObj_ext
      · change (Ψ ≫ F) ≫ (fst G G).left = (c ≫ φ₂) ≫ (fst G G).left
        rw [Category.assoc, Category.assoc, hsq.1, hF1, ← Category.assoc, hΨ2, ← Category.assoc, hc1,
          Category.assoc, Category.assoc, hzl]
      · change (Ψ ≫ F) ≫ (snd G G).left = (c ≫ φ₂) ≫ (snd G G).left
        rw [Category.assoc, Category.assoc, hsq.2, hF2, hΨ1, ← Category.assoc, hc2]
    have e1 : LBIso (P.pull c) (P'.pull (Ψ ≫ F)) := GenSpread.lbIso_pull_of_lbIso hPP' c hc
    have e2 : LBIso (P'.pull (Ψ ≫ F)) ((P'.pull F).pull Ψ) := GenSpread.lbIso_pull_pull hP' Ψ rfl
    obtain ⟨s', hs'⟩ := RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP' F) Ψ) (pull_isLB hP' _) e2.symm
      (LB.genPull _ s Ψ) (LB.isGen_genPull _ s hs Ψ)
    have hzk := RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hP c) e1.symm s' hs'
    have hzm : z ^ m = 1 := hA T' z hzk
    rw [MonObj.comp_pow, MonObj.comp_one, ← hz]
    show pushHom hpb T' z ^ m = 1
    rw [← map_pow, hzm, map_one]
  rw [← MonObj.comp_pow, key, MonObj.comp_one]

end GlobalTheory.KerExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPullbackRefinementStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedIdempotentFactor_pullback_refinement : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
  ∀ (Q : Data R) (D' : DegPre R) (F : PFactor Q D') (D : DegPre R') (ε : D.X ≃+ Q.X), Refines Q ρ D ε →
  ∀ (D₁' : DegPre R') (hD' : IsPullDeg ρ D' D₁') [Module F.O D₁'.X] (o₁ : D₁'.OAct F.O),
    (∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y) →
    (∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) →
    ∃ (inc : D.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D.P.A) (xi : D.X →+ D₁'.X) (xp : D₁'.X →+ D.X)
      (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.FactorPull.pfactor_pull | exact GlobalTheory.FactorPull.pfactor_pull | (intros; apply GlobalTheory.FactorPull.pfactor_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  first | exact @GlobalTheory.Mum.thetaNZ_of_preU | exact GlobalTheory.Mum.thetaNZ_of_preU | (intros; apply GlobalTheory.Mum.thetaNZ_of_preU <;> assumption)
end

