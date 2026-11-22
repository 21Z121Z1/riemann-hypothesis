import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0116
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointWithCharactersIffPullDeg
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeForms
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.FibCone

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

theorem isIntegral_G {k : Type} [Field k] (Φ : FibPre k) : IsIntegral Φ.G.left := by
  have h : IsSemiAbelian Φ.G := GlobalTheory.isSemiAbelian_of_isGt _ Φ.E Φ.G ⟨Φ.D⟩
  have := h.smooth
  have := h.geomConnected
  have : GeometricallyIntegral Φ.G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ Φ.G
  exact GeometricallyIntegral.isIntegral_of_subsingleton Φ.G.hom

theorem exists_ne_zero_of_mem_cone {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) (J₀ : Set J) (hH : H.IsLB) (hc : ⨆ i ∈ J₀, Out.nonzeroLocus (s i) = ⊤) (v : J → k)
    (hv : v ∈ cone p H s) : ∃ i ∈ J₀, v i ≠ 0 := by
  obtain ⟨x, -, hx⟩ := hv
  let pt : Sp k := IsLocalRing.closedPoint k
  have hm : x pt ∈ (⨆ i ∈ J₀, Out.nonzeroLocus (s i)) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi, hm⟩ := hm
  refine ⟨i, hi, ?_⟩
  have hu := (((GlobalTheory.ZH.CrdCalc.crd_calculus X H J s hH).1 k x).2.2 v i hx).2 (by
    intro y _
    have : y = pt := Subsingleton.elim (α := PrimeSpectrum k) _ _
    subst this
    exact hm)
  exact hu.ne_zero

theorem mem_cone_iff : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg hN hsm hh v
  have hH := Φ.H_isLB 1
  have himm := GlobalTheory.T.immBy_weight_zero' hL hL2 k Φ g N N' q J cls F π hB hG hg
  constructor
  · intro hv
    exact ⟨exists_ne_zero_of_mem_cone _ _ F _ hH himm.1 v hv, fun d Pf hd hP ht =>
      GlobalTheory.T.form_vanishes_of_torsion_torusExtension hL hL2 k Φ g N N' q J cls F π hB hG hg hN d Pf hd hP ht v hv⟩
  · rintro ⟨h0, hv⟩
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous k _ Φ.G.hom (Φ.H 1) J F _ hH himm (isIntegral_G Φ) g hsm
    refine GlobalTheory.ZH.ConeClosed.mem_cone_of_vanishing k _ Φ.G.hom (Φ.H 1) J F _ hH himm v h0 ?_
    refine eval_eq_zero_of_hilb_le k J _ g N h1 h2 h3 h4 hh v fun d Pf hd hP hI => hv d Pf hd hP ?_
    intro x _
    obtain ⟨w, hw⟩ := ((GlobalTheory.ZH.CrdCalc.crd_calculus _ (Φ.H 1) J F hH).1 k x.left).1
    refine ⟨w, hw, ?_⟩
    have := (MvPolynomial.mem_vanishingIdeal_iff.1 hI) w ⟨x.left, Over.w x, hw⟩
    simpa [MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ZH.FibCone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickeningStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_lift_squareZero_thickening : ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X : Over (Spec (CommRingCat.of A))) (X' : Over (Spec (CommRingCat.of A'))) (β : X'.left ⟶ X.left), IsPullback β X'.hom X.hom (Spec.map (CommRingCat.ofHom g)) → LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull β) → RelAmple X' L' → RelAmple X L := by
  first | exact @GlobalTheory.AmpleThickening.relAmple_of_sq_zero | exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero | (intros; apply GlobalTheory.AmpleThickening.relAmple_of_sq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfFiniteEtaleIsogeny
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem relAmple_of_finite_etale_isogeny : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → ∀ (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → LBIso L (M.pull ψ.left) → Out.RelAmple A L → Out.RelAmple B M := by
  intro k _ _ A B _ _ hA hB ψ _ hf he hs L M hL hM hiso hamp
  have hN : IsLocallyNoetherian (Sp k) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have h₁ := (GlobalTheory.relAmple_finite_pow_iso (Sp k) A A (𝟙 A) L 1 one_pos hA hA hL
    (by simpa using (inferInstance : IsFinite (𝟙 A.left)))).2.2.2 (M.pull ψ.left) (LB.isLB_pull hM ψ.left) hiso hamp
  exact (GlobalTheory.relAmple_finite_pow_iso (Sp k) A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs h₁

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecGenericEqMulTheta
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ThetaLine
open GlobalTheory.Points

variable {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ)

theorem le_chart {T : Over B} {K : Type} [CommRing K] (q : Sp K ⟶ (T ⊗ A).left) (j : L.ι)
    (h : Set.range (q ≫ (snd T A).left) ⊆ L.U j) : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T).U (fun _ => j) :=
  fun y _ => Set.mem_iInter.2 fun _ => h ⟨y, rfl⟩

theorem valR_pull [GrpObj A] {T T' : Over B} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s')
    {K : Type} [CommRing K] (q : Sp K ⟶ (T' ⊗ A).left) (j : Fin 1 → L.ι) (hq : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T').U j) :
    valR q _ (s'.f j) = valR (q ≫ h.left) _ (s.f j) := by
  rw [H j, valR_res q _ hq, valR_comp]

theorem valR_of_basis {Ω : Type} [CommRing Ω] (t : Sp Ω ⟶ B) {m : ℕ} (hm : m = 1)
    {b : Fin m → LB.Sec (LPow A L a (Over.mk t))} (hb : IsSecBasis _ b) :
    ∃ b₀ : LB.Sec (LPow A L a (Over.mk t)), ∀ s : LB.Sec (LPow A L a (Over.mk t)), ∃ c : Ω,
      ∀ (K : Type) [CommRing K] (β : Ω →+* K) (q : Sp K ⟶ (Over.mk t ⊗ A).left) (j : Fin 1 → L.ι),
        q ≫ (fst (Over.mk t) A).left = spMap β → ⊤ ≤ q ⁻¹ᵁ (LPow A L a (Over.mk t)).U j →
        valR q _ (s.f j) = β c * valR q _ (b₀.f j) := by
  subst hm
  refine ⟨b 0, fun s => ?_⟩
  obtain ⟨r, hr, -⟩ := hb s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0), fun K _ β q j hq hj => ?_⟩
  rw [hr j, Fin.sum_univ_one, valR_mul q _ hj, valR_res q _ hj]
  congr 1
  have e := valR_comp q (fst (Over.mk t) A).left ⊤ (r 0)
  refine e.symm.trans ?_
  rw [hq]
  have e2 := valR_specMap (C := K) (A := CommRingCat.of Ω) (CommRingCat.ofHom β)
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0))
  refine Eq.trans ?_ e2
  exact congrArg (valR (spMap β) ⊤) ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom_inv_id_apply (r 0)).symm

theorem valR_ne_zero [GrpObj A] {T : Over B} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [Field K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) (hv : valR x ⊤ v ≠ 0) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) ≠ 0 := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  refine e.trans_ne (mul_ne_zero hv ?_)
  rw [valR_eq x _ hx]
  exact ((τ.s fun _ => j).isUnit.map _).ne_zero

end GlobalTheory.ZH.ThetaLine

open GlobalTheory.Points GlobalTheory.ZH.ThetaLine in

theorem GlobalTheory.ZH.sec_generic_eq_mul_theta : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)))), ∃ c : Ω, ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → Set.range (q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → valF q _ (s.f fun _ => jP) = β c * valF r _ (ρ.th₁.f fun _ => jP) := by
  intro _ hL2 o Ω _ _ _ _ S ρ s
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  let h : (Over.mk t₀ : Over (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk t₀ (Category.comp_id t₀)
  obtain ⟨th, hth⟩ : ∃ th, IsPullSec ρ.P.A ρ.P.L 1 (h ▷ ρ.P.A) (whiskerRight_snd h ρ.P.A) ρ.th₁ th :=
    (GlobalTheory.LN.PolFrames.exists_pullSec ρ.P.A ρ.P.L 1 h ρ.th₁).imp fun _ H => H.1
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hL2.secTwist ρ.P 1 le_rfl Ω t₀
  obtain ⟨b₀, hb₀⟩ := valR_of_basis ρ.P.A ρ.P.L 1 t₀ (one_pow _) hb
  obtain ⟨c, hc⟩ := hb₀ s
  obtain ⟨d, hd⟩ := hb₀ th
  have hd0 : d ≠ 0 := by
    obtain ⟨a, ha⟩ := S.th_ne
    obtain ⟨j, hj⟩ := exists_chart ρ.P.isLB ((t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω))
    have hj' : Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U j := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]
      exact hj
    have hne := valR_ne_zero ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ j hj'
      ((valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _).trans_ne ha)
    let x : Sp Ω ⟶ ((Over.mk t₀ : Over (Sp S.R)) ⊗ ρ.P.A).left := (ptSecT ρ.P.A (h ≫ ρ.pt a)).left
    have hx1 : x ≫ (fst (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = spMap (RingHom.id Ω) :=
      (congrArg CommaMorphism.left (lift_fst (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))).trans (Spec.map_id _).symm
    have hx2 : x ≫ (snd (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = t₀ ≫ (ρ.pt a).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))
    have hx3 : x ≫ (h ▷ ρ.P.A).left = t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left := by
      have : ptSecT ρ.P.A (h ≫ ρ.pt a) ≫ h ▷ ρ.P.A = h ≫ ptSecT ρ.P.A (ρ.pt a) := by
        simp [ptSecT]
      exact congrArg CommaMorphism.left this
    have hxj := le_chart ρ.P.A ρ.P.L 1 x j (hx2 ▸ hj')
    rintro rfl
    apply hne
    rw [← hx3, ← valR_pull ρ.P.A ρ.P.L 1 hth x _ hxj, hd Ω _ x _ hx1 hxj, map_zero, zero_mul]
  refine ⟨c / d, fun K _ β q r j hq hr hj => ?_⟩
  have hqj := le_chart ρ.P.A ρ.P.L 1 q j hj
  have hrq : r = q ≫ (h ▷ ρ.P.A).left := by
    have h2 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        (q ≫ (h ▷ ρ.P.A).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left := by
      rw [hr, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have w : (fst (baseOver (Sp S.R)) ρ.P.A).left =
        (snd (baseOver (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom :=
      (Category.comp_id _).symm.trans (pullback.condition (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom))
    refine pullback.hom_ext (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom) ?_ h2
    change r ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = _ ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left
    rw [w, ← Category.assoc, h2]
    simp only [Category.assoc]
  change valR q _ _ = β (c / d) * valR r _ _
  rw [hrq, ← valR_pull ρ.P.A ρ.P.L 1 hth q _ hqj, hc K β q _ hq hqj, hd K β q _ hq hqj, map_div₀,
    ← _root_.mul_assoc, div_mul_cancel₀ _ ((map_ne_zero β).2 hd0)]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtensionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S Z : Scheme.{0}) (t₀ : SAB H S) (t : SAB H Z) (π : Z ⟶ S) (_ : SABMap t t₀ π) (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [CommRing R] [IsDomain R] [CharZero R] (g : R₁ →+* R) (gam : FractionRing R₁ →+* FractionRing R), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R _ (g r)) → ∀ (x₁ : Sp (FractionRing R₁) ⟶ S) (x : Sp (FractionRing R) ⟶ Z), x ≫ π = spMap gam ≫ x₁ → PolAt t₀ x₁ → ∀ (N n : ℕ) (f₁ : Fin n → LB.Sec (LPow t₀.G t₀.PP.L (N : ℤ) (Over.mk x₁))), IsFrame t₀.G t₀.PP.L N x₁ f₁ → ∃ f : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk x)), IsFrame t.G t.PP.L N x f ∧ BasisAlong t.G t.PP.L N (𝟙 _) f := by
  first | exact @GlobalTheory.FramePull.frame_pull | exact GlobalTheory.FramePull.frame_pull | (intros; apply GlobalTheory.FramePull.frame_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testModel_maps_into_openPart : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ⊤ ≤ (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G := by
  first | exact @GlobalTheory.ZH.TestInOpen.top_le_preimage_G | exact GlobalTheory.ZH.TestInOpen.top_le_preimage_G | (intros; apply GlobalTheory.ZH.TestInOpen.top_le_preimage_G <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointWithCharactersIffPullDegStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPoint_with_characters_iff_pullDeg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left → (∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ D.Oφ g.pG (hD.xe x) k, LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x) (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ (g.t (hD.xe x)))) → ∀ (T : Scheme.{0}) (z : T ⟶ (thickObj R' I' e G').left) (a : D'.X → Γ(T, ⊤)), (∃ τ' : T ⟶ (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left, τ' ≫ g'.i.left = z ∧ ∀ x, τ'.appTop.hom (charUnit _ D'.X x).val = a x) ↔ ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z ≫ h ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (hD.xe x)).val = a x := by
  first | exact @GlobalTheory.TorusPull.torus_point_iff | exact GlobalTheory.TorusPull.torus_point_iff | (intros; apply GlobalTheory.TorusPull.torus_point_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxCosetNormGe
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.TwistCoset

theorem tx_eq_of_qEq {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) {m : ℕ} (hm : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  refine Eq.trans (tsum_congr fun χ => ?_) ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)
  exact (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2

variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {l : ℕ}

theorem twRel_mul {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a') (hb : TwRel β u r b b') :
    TwRel β u r (a * b) (a' * b') := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨congrArg₂ (fun s t : Multiplicative N.X => s * t) a1 b1,
    congrArg₂ (fun s t : N.A => s * t) a2 b2, fun z => ?_⟩
  change a'.1.2.s z * b'.1.2.s z / N.θ (N.c z) a'.1.2.b b'.1.2.b =
    a.1.2.s z * b.1.2.s z / N.θ (N.c z) a.1.2.b b.1.2.b * r ^ β.be (a.1.1.toAdd + b.1.1.toAdd) z
  rw [a2, b2, a3, b3, map_add, LinearMap.add_apply, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twRel_qEq (hr : r ^ l = u) {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a')
    (hb : TwRel β u r b b') (h : N.QEq a b) : (N.twist β u).QEq a' b' := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (w : N.X) => ?_)⟩
  · rw [a1, b1]; exact h1
  · refine b2.trans ?_
    rw [h2]
    exact congrArg (fun s : N.A => s * N.c z) a2.symm
  · change b'.1.2.s w = a'.1.2.s w * (N.twist β u).τ z w / N.θ (N.c w) a'.1.2.b (N.c z)
    have e : r ^ ((l : ℤ) * β.be z w) = u ^ β.be z w := by rw [zpow_mul, zpow_natCast, hr]
    rw [b3, a3, a2, N.twist_τ, h1, h2, NumD.Gt.mul_s, NumD.io_s, NumD.io_b, map_add, LinearMap.add_apply, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul, zpow_add, e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]; abel

theorem exists_twRel_of_eq_one (r : Oˣ) (h : (N.twist β u).QT l) (h1 : h.1.1 = 1) {e : ℕ} (he : h.1.2 ^ e = 1) :
    ∃ h₀ : N.QT l, h₀ ^ e = 1 ∧ TwRel β u r h₀ h := by
  let f : (N.twist β u).Gt →* N.Gt := MonoidHom.mk' (fun g => ⟨g.b, g.s, g.mult⟩) fun _ _ => rfl
  have hl : h.1.2 ^ l = 1 := by
    rw [(N.twist β u).mem_QT.1 h.2, h1]; exact (N.twist β u).io_zero
  refine ⟨⟨(1, f h.1.2), ?_⟩, Subtype.ext (Prod.ext (one_pow e) ?_), h1, rfl, fun z => ?_⟩
  · rw [NumD.mem_QT, ← map_pow, hl, map_one]; exact N.io_zero.symm
  · change f h.1.2 ^ e = 1
    rw [← map_pow, he, map_one]
  · change h.1.2.s z = h.1.2.s z * r ^ β.be 0 z
    rw [map_zero, LinearMap.zero_apply, zpow_zero, mul_one]

variable {La : Type} [AddCommGroup La] {q : La → N.QT l}

theorem qEq_zero (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) : N.QEq (q 0) 1 := by
  have := TateInh.qEq_mul N (hq 0 0) ((N.qEq_equivalence l).refl (q 0)⁻¹)
  rwa [add_zero, mul_inv_cancel_right, mul_inv_cancel] at this

theorem qEq_nsmul (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) (a : La) (e : ℕ) : N.QEq (q a ^ e) (q (e • a)) := by
  have E := N.qEq_equivalence l
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact E.symm (qEq_zero hq)
  | succ e ih => rw [pow_succ, succ_nsmul]; exact E.trans (TateInh.qEq_mul N ih (E.refl _)) (hq _ _)

theorem qEq_pow {a b : N.QT l} (h : N.QEq a b) (e : ℕ) : N.QEq (a ^ e) (b ^ e) := by
  induction e with
  | zero => rw [pow_zero, pow_zero]; exact (N.qEq_equivalence l).refl _
  | succ e ih => rw [pow_succ, pow_succ]; exact TateInh.qEq_mul N ih h

theorem eq_zero_of_pow_nsmul {n : ℕ} (hn : ∀ a : La, n • a = 0 → a = 0) (e : ℕ) (a : La) (h : n ^ e • a = 0) :
    a = 0 := by
  induction e with
  | zero => rwa [pow_zero, one_smul] at h
  | succ e ih => exact ih (hn _ (by rwa [pow_succ', mul_smul] at h))

end GlobalTheory.TwistCoset

open GlobalTheory.TwistCoset in

theorem GlobalTheory.twist_tx_coset_norm_ge : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (k : ℕ) (β : N.Form k) (u r : Cˣ) (qf : QuadraticMap ℤ N.X ℝ) (n g j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 1 ≤ j → ‖(u : C)‖ < 1 → r ^ ((n ^ j) ^ 2) = u → (N.twist β u).Int qf → (∀ y, qf y = -Real.log ‖(u : C)‖ * ((β.be y y : ℝ) / 2)) → N.Tors n g → ∀ (La : Type) [AddCommGroup La] (q : La → N.QT ((n ^ j) ^ 2)), (∀ a : La, n • a = 0 → a = 0) → (∀ a b, N.QEq (q a * q b) (q (a + b))) → (∀ a b, N.QEq (q a) (q b) ↔ ∃ e, a = b + (n ^ j) ^ 2 • e) → (∀ p, ∃ a, N.QEq (q a) p) → ∀ p : La → (N.twist β u).QT ((n ^ j) ^ 2), (∀ x, TwRel β u r (q x) (p x)) → (∃ x, 1 ≤ ‖(N.twist β u).tx (n ^ j) (p x)‖) ∧ ∀ x, ∃ h, ‖(u : C)‖ ^ (β.be (q x).1.1.toAdd (q x).1.1.toAdd).toNat ≤ ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • h))‖ := by
  intro C _ _ _ _ N k β u r qf n g j hp ho hn hj hu hr hI hqf hT La _ q htf hadd hker honto p hpq
  have hm : Odd (n ^ j) := ho.pow
  have E := N.qEq_equivalence ((n ^ j) ^ 2)
  have hP : qf.PosDef := GlobalTheory.CosetCrit.posDef_of_tendsto (X := N.X) hI.pos
  have key : ∀ (x : La) (χ₀ : N.X), (∀ χ : N.X, qf ((q x).1.1.toAdd + n ^ j • χ₀) ≤ qf ((q x).1.1.toAdd + n ^ j • χ)) →
      ∃ e, Real.exp (-(qf ((q x).1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤
        ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • e))‖ := fun x χ₀ h₀ => by
    obtain ⟨h, h1, h2, h3⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge (N := N.twist β u) (q := qf) hI hp ho hn hT hj (p x)
      (χ₀ := χ₀) (by rw [(hpq x).1]; exact h₀)
    obtain ⟨h', h4, h5⟩ := exists_twRel_of_eq_one r h h1 h2
    obtain ⟨a, ha⟩ := honto h'
    have h6 : N.QEq (q (n ^ (j + 1) • a)) (q 0) := by
      have := qEq_pow ha (n ^ (j + 1))
      rw [h4] at this
      exact E.trans (E.symm (qEq_nsmul hadd a _)) (E.trans this (E.symm (qEq_zero hadd)))
    obtain ⟨e, he⟩ := (hker _ _).1 h6
    have h7 : a = n ^ (j - 1) • e := by
      refine sub_eq_zero.1 (eq_zero_of_pow_nsmul htf (j + 1) _ ?_)
      rw [smul_sub, he, zero_add, ← mul_smul, ← pow_add, ← pow_mul, show j + 1 + (j - 1) = j * 2 by omega, sub_self]
    refine ⟨e, ?_⟩
    have h8 : N.QEq (q x * h') (q (x + a)) := E.trans (TateInh.qEq_mul N (E.refl _) (E.symm ha)) (hadd x a)
    rw [← h7, tx_eq_of_qEq _ hm (twRel_qEq hr (twRel_mul (hpq x) h5) (hpq (x + a)) h8)]
    rw [(hpq x).1] at h3
    exact h3
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨z, hz, -⟩ := E.symm (qEq_zero hadd)
    have hz0 : (q 0).1.1.toAdd + n ^ j • (-(n ^ j • z)) = 0 := by
      rw [hz, smul_neg, ← mul_smul, ← sq]
      exact (congrArg (· + -((n ^ j) ^ 2 • z)) (zero_add _)).trans (add_neg_cancel _)
    obtain ⟨e, he⟩ := key 0 (-(n ^ j • z)) fun χ => by rw [hz0, map_zero]; exact hP.nonneg _
    rw [hz0, map_zero, zero_div, neg_zero, Real.exp_zero] at he
    exact ⟨_, he⟩
  · obtain ⟨χ₀, h₀⟩ := (GlobalTheory.CosetCrit.tendsto_class (X := N.X) (q := qf) hI.pos (q x).1.1.toAdd
      hm.pos.ne').exists_forall_le
    obtain ⟨e, he⟩ := key x χ₀ h₀
    refine ⟨e, le_trans ?_ he⟩
    have h1 := h₀ 0
    rw [smul_zero, add_zero, hqf (q x).1.1.toAdd] at h1
    have h2 := hP.nonneg ((q x).1.1.toAdd + n ^ j • χ₀)
    set y := (q x).1.1.toAdd
    have hB : 0 ≤ β.be y y := by
      by_cases hy : y = 0
      · rw [hy, map_zero]
      · exact (β.pos y hy).le
    have h0 : 0 < ‖(u : C)‖ := norm_pos_iff.2 u.ne_zero
    have hL : Real.log ‖(u : C)‖ < 0 := Real.log_neg h0 hu
    have hc : (((β.be y y).toNat : ℕ) : ℝ) = (β.be y y : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hB]
    have hB' : (0 : ℝ) ≤ (β.be y y : ℝ) := by exact_mod_cast hB
    have hsq : (1 : ℝ) ≤ ((n ^ j : ℕ) : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm.pos)
    have h3 := div_le_self h2 hsq
    rw [← Real.exp_log (pow_pos h0 _), Real.log_pow, hc]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hB' (neg_pos.2 hL).le]
end

