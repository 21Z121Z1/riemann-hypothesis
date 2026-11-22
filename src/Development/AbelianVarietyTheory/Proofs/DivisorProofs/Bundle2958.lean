import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFacts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem cmp_mul (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x y : N'.A) (j : Fin r) :
    cmp T ν ν' (x * y) j = cmp T ν ν' x j * cmp T ν ν' y j := by
  haveI := T.pr_hom j
  simp only [TensTor.cmp, map_mul]
  rw [← map_mul ν.eA.symm]
  congr 1
  exact GlobalTheory.TorusDefect.mul_comp_of_pullback (jK R) (T.pr j) (jFK F) (jFK F ≫ jK R) rfl (ν'.eA x) (ν'.eA y)

theorem cmp_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (cmp T ν ν') := by
  constructor
  · intro x y h
    apply ν'.eA.injective
    refine Fan.IsLimit.hom_ext T.lim _ _ fun j => ?_
    have := congrFun h j
    simpa [TensTor.cmp] using this
  · intro f
    refine ⟨ν'.eA.symm (Fan.IsLimit.lift T.lim fun j => ν.eA (f j)), funext fun j => ?_⟩
    simp only [TensTor.cmp, MulEquiv.apply_symm_apply]
    refine (congrArg ν.eA.symm (Fan.IsLimit.fac T.lim _ j)).trans ?_
    simp

theorem chi_add (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ χ' : N'.X) (i : Fin r) :
    chi T ν ν' (χ + χ') i = chi T ν ν' χ i + chi T ν ν' χ' i := by
  simp [TensTor.chi, map_add]

theorem chi_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (chi T ν ν') := by
  have : chi T ν ν' = ν'.eX.trans (T.xe.trans (AddEquiv.piCongrRight fun _ => ν.eX.symm)) := by
    funext χ i; rfl
  rw [this]; exact AddEquiv.bijective _

theorem cmp_c (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ' : N'.X) (j : Fin r) :
    cmp T ν ν' (N'.c χ') j = N.c (chi T ν ν' χ' j) := by
  simp only [TensTor.cmp, TensTor.chi]
  rw [ν.eA.symm_apply_eq, ν.c_eq, ν'.c_eq, ν.eX.apply_symm_apply]
  simp only [DegPre.cF, Category.assoc, T.c_pr]

theorem wv_ne_zero (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : wv T ν ν' x ≠ 0 := by
  unfold TensTor.wv valF
  rw [dif_pos]
  · exact (((T.w.s _).isUnit.map _).map _).ne_zero
  · intro p _
    refine ⟨Set.mem_iInter.2 fun k => ?_, ν'.good _ trivial⟩
    exact ν.good ((ν'.eA x).left ≫ tensφ T.pr k) (show p ∈ (⊤ : (Sp F).Opens) from trivial)

end GlobalTheory.Mum.TensTor

open GlobalTheory.Mum.TensTor in

theorem GlobalTheory.Mum.TensTor.tensFacts_holds : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), TensFacts W (cmp T ν ν') (chi T ν ν') (wv T ν ν') := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν'
  exact ⟨cmp_mul T ν ν', cmp_bijective T ν ν', chi_add T ν ν', chi_bijective T ν ν', cmp_c T ν ν', wv_ne_zero T ν ν',
    GlobalTheory.T.tensorData_cubicalStructure_values R hB D D' W T F N N' ν ν', GlobalTheory.T.tensorData_psi_values_through_bundleIso R hB D D' W T F N N' ν ν'⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  first | exact @GlobalTheory.TensPsiCoord.main | exact GlobalTheory.TensPsiCoord.main | (intros; apply GlobalTheory.TensPsiCoord.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThListConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalConj
open GlobalTheory.UMin.GalTh

theorem coe_mul {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ₁ τ₂ : K ≃ₐ[Ω] K) :
    ((τ₁ * τ₂ : K ≃ₐ[Ω] K) : K →+* K) = (τ₁ : K →+* K).comp (τ₂ : K →+* K) := RingHom.ext fun _ => rfl

theorem coe_one {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] :
    ((1 : K ≃ₐ[Ω] K) : K →+* K) = RingHom.id K := RingHom.ext fun _ => rfl

theorem comp_alg {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ : K ≃ₐ[Ω] K) :
    (τ : K →+* K).comp (algebraMap Ω K) = algebraMap Ω K := RingHom.ext fun r => τ.commutes r

theorem thList_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω K : Type) [Field Ω] [Field K] [IsAlgClosed K] [Algebra Ω K] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ G)) (c : Fin N → K), Odd m → (m : K) ≠ 0 → PolFib G L g (spMap (algebraMap Ω K) ≫ x) → ThList G L ρ m (spMap (algebraMap Ω K) ≫ x) (SecAt.pull G L θ (algebraMap Ω K)) pt c → ∃ φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N), ∀ (τ : K ≃ₐ[Ω] K) (a : Fin N), spMap (τ : K →+* K) ≫ (pt a).left = (pt (φ τ a)).left ∧ τ (c a) = c (φ τ a) := by
  intro S G _ _ L ρ hL hρ g m N Ω K _ _ _ _ x θ pt c hm hmK hpol hK
  classical
  have hfix : ∀ τ : K ≃ₐ[Ω] K, spMap (τ : K →+* K) ≫ (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom = (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom := fun τ => by
    show spMap (τ : K →+* K) ≫ spMap (algebraMap Ω K) ≫ x = spMap (algebraMap Ω K) ≫ x
    rw [← Category.assoc, ← GalTh.sp_comp, comp_alg]
  let u : (K ≃ₐ[Ω] K) → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ Over.mk (spMap (algebraMap Ω K) ≫ x)) := fun τ => Over.homMk (spMap (τ : K →+* K)) (hfix τ)
  have hul : ∀ τ, (u τ).left = spMap (τ : K →+* K) := fun τ => Over.homMk_left _ _
  have hu1 : u 1 = 𝟙 _ := Over.OverMorphism.ext (by rw [hul, coe_one, GalTh.sp_id]; rfl)
  have humul : ∀ τ₁ τ₂, u (τ₁ * τ₂) = u τ₁ ≫ u τ₂ := fun τ₁ τ₂ =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hul, hul, hul, coe_mul, GalTh.sp_comp])
  have htor : ∀ τ a, (u τ ≫ pt a) ^ (m ^ 2) = 1 := fun τ a => by
    rw [← MonObj.comp_pow, (hK.2.1 a).1, MonObj.comp_one]
  choose f hf using fun τ a => thList_exh hK (u τ ≫ pt a) (htor τ a)
  have hf1 : ∀ a, f 1 a = a := fun a => hK.1 (by rw [← hf, hu1, Category.id_comp])
  have hfmul : ∀ τ₁ τ₂ a, f (τ₁ * τ₂) a = f τ₁ (f τ₂ a) := fun τ₁ τ₂ a => hK.1 (by
    rw [← hf, ← hf, ← hf, humul, Category.assoc])
  let P : (K ≃ₐ[Ω] K) → Equiv.Perm (Fin N) := fun τ =>
    { toFun := f τ, invFun := f τ⁻¹
      left_inv := fun a => by rw [← hfmul, inv_mul_cancel, hf1]
      right_inv := fun a => by rw [← hfmul, mul_inv_cancel, hf1] }
  let φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N) :=
    { toFun := P
      map_one' := Equiv.ext fun a => hf1 a
      map_mul' := fun τ₁ τ₂ => Equiv.ext fun a => hfmul τ₁ τ₂ a }
  have hφ : ∀ τ a, φ τ a = f τ a := fun _ _ => rfl
  have hleft : ∀ (τ : K ≃ₐ[Ω] K) a, spMap (τ : K →+* K) ≫ (pt a).left = (pt (f τ a)).left := fun τ a => by
    rw [← hf, Over.comp_left, hul]
  refine ⟨φ, fun τ a => ⟨by rw [hφ]; exact hleft τ a, ?_⟩⟩
  rw [hφ]
  obtain ⟨pt', hpt', h'⟩ := GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N K K (τ : K →+* K) (spMap (algebraMap Ω K) ≫ x)
    (SecAt.pull G L θ (algebraMap Ω K)) pt c hK
  obtain ⟨pt₃, hpt₃, h₃⟩ := thList_comp m (algebraMap Ω K) (τ : K →+* K) (algebraMap Ω K) (comp_alg τ) x θ pt' _ h'
  have e3 : pt₃ a = pt (f τ a) := Over.OverMorphism.ext (by rw [hpt₃, hpt', hleft])
  have q := h₃.2.1 a
  rw [e3] at q
  have hθ : SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) =
      @id Γ((Over.mk (spMap (algebraMap Ω K) ≫ x)).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) := by
    rw [id, show GlobalTheory.ZH.fn (1 : K) = 1 from map_one _, one_smul]
  have r := (GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g m K (spMap (algebraMap Ω K) ≫ x) _ _ (pt (f τ a)) 1 (c (f τ a)) (τ (c a)) hm hmK hpol hθ
    (hK.2.1 (f τ a))).1 q
  rw [r, _root_.one_mul]

end GlobalTheory.UMin.GalConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantKthRootLabelledPointUpToRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.thetaConst_pow_eq_at_root | exact GlobalTheory.thetaConst_pow_eq_at_root | (intros; apply GlobalTheory.thetaConst_pow_eq_at_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_unique_and_linear_in_section : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K), Odd m → (m : K) ≠ 0 → PolFib G L g x → SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ → ThG G L ρ m θ p (GlobalTheory.ZH.fn c) → (ThG G L ρ m θ' p (GlobalTheory.ZH.fn c') ↔ c' = a * c) := by
  first | exact @GlobalTheory.UMin.thG_smul_iff | exact GlobalTheory.UMin.thG_smul_iff | (intros; apply GlobalTheory.UMin.thG_smul_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  first | exact @GlobalTheory.UMin.thG_unique_of_polFib | exact GlobalTheory.UMin.thG_unique_of_polFib | (intros; apply GlobalTheory.UMin.thG_unique_of_polFib <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_firstJets_linearIndependent : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  first | exact @GlobalTheory.MBLow.TRank.main | exact GlobalTheory.MBLow.TRank.main | (intros; apply GlobalTheory.MBLow.TRank.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaF
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CovTest GlobalTheory.LineForm

namespace GlobalTheory.FibGlob

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

def thetaF (hY : IsRegVar p d) (σ : k →+* ℂ) {E : Y.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    (hY.atlas σ).Pt → Ev d :=
  c1F hY σ (VMetric.grLB fl 0 H) + omF hY σ m fl

def c1EF (hB : IsRegVar q d) (σ : k →+* ℂ) {E : B.Modules} (m : VMetric q E 2) (fl : Vert.Flag E 2) :
    (hB.atlas σ).Pt → Ev d :=
  fun x => (hB.atlas σ).chern ((m.met σ).gram (frameAt fl x.pt).frame) 1 x

end GlobalTheory.FibGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilySectionEquivarianceSmulOfNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.ScaleEqv

theorem eqv_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ D A F _ _ N lab E h c
  let gg : F →+* Γ((TFK (R := R) F ⊗ A.A).left, ⊤) :=
    (fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hgg : ∀ u : F, gg u = (fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F u) := fun _ => rfl
  have inv1 : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens) (u : Fˣ), resTop W (gg u.val) * resTop W (gg (u⁻¹).val) = 1 := by
    intro W u
    simp only [resTop]
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let S : F → SecK A.L (snd (TFK (R := R) F) A.A).left N → SecK A.L (snd (TFK (R := R) F) A.A).left N :=
    fun u t => DVR.SecOps.secScale (gg u) t
  have Sf : ∀ u t j, (S u t).f j = resTop _ (gg u) * t.f j := fun _ _ _ => rfl
  have SS : ∀ (u : Fˣ) t, S u.val (S (u⁻¹).val t) = t := by
    intro u t
    apply DVR.SecOps.sec_ext
    intro j
    rw [Sf, Sf, ← _root_.mul_assoc, inv1, _root_.one_mul]
  have SS' : ∀ (u : Fˣ) t, S (u⁻¹).val (S u.val t) = t := by
    intro u t
    have := SS u⁻¹ t
    rwa [inv_inv] at this
  refine ⟨fun s => S c.val (E s), ⟨?_, ?_, ?_, h.onto, h.frame, h.lift, ?_⟩, fun s j => rfl⟩
  · constructor
    · intro s t hst
      apply h.bij.1
      have := congrArg (S (c⁻¹).val) hst
      simpa only [SS'] using this
    · intro t
      obtain ⟨s, hs⟩ := h.bij.2 (S (c⁻¹).val t)
      exact ⟨s, by simp only [hs, SS]⟩
  · intro s s' s'' hs j
    simp only [Sf]
    rw [h.add s s' s'' hs j, mul_add]
  · intro u s s' hs j
    simp only [Sf]
    rw [h.smul u s s' hs j, mul_left_comm]
  · intro p w θ s s' hw hθ hph j
    have key := h.act p w θ s s' hw hθ hph j
    have e : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by
      rw [← Over.comp_left, translT, lift_fst]
    have hψ : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens),
        ((translT A.A θ.pt).left.app W).hom (resTop W (gg c.val)) =
          resTop ((translT A.A θ.pt).left ⁻¹ᵁ W) (gg c.val) := by
      intro W
      simp only [resTop]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      congr 1
      rw [hgg]
      have hT : ((translT A.A θ.pt).left.appTop).hom (((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val)) =
          ((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
      exact hT
    erw [Sf, Sf]
    erw [map_mul, map_mul, map_mul, hψ, key, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, mul_left_comm]

end GlobalTheory.Mum.ScaleEqv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTranslatedMembersLeadingTimesIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_translatedMembers_leading_times_integral : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ), GlobalTheory.ThFam.Reads D.toPre κ → ∀ (k : ℕ), 1 ≤ k → ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (F : Fam D.toPre (FractionRing R) k), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) → ∀ (mu : D.toPre.X) (r : R), algebraMap R (FractionRing R) r = ((GlobalTheory.ThFam.lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) → ∃ f : D.toPre.SecB k (α + k • mu), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) (α + k • mu)) (DegPre.famε k) (F.s (α + k • mu)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ ∀ e : ℕ, r ∈ maximalIdeal R ^ (e + 1) → VanMod (maximalIdeal R) f e := by
  first | exact @GlobalTheory.ThFam.member_integral | exact GlobalTheory.ThFam.member_integral | (intros; apply GlobalTheory.ThFam.member_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem isActOf_of_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  intro S S' A A' _ _ L L' hL hL' T T' f _ k θ θ' Ψ hT H σ σ' τ τ' hσ hσ' hact
  refine GlobalTheory.ThetaNu.isActOf_of_sval hL fun y J hJ => ?_
  choose J' hJ' using fun χ : (T ⊗ A).left ⟶ A'.left => exists_chart hL' (χ y)
  have gJ' : Good L' y J' := hJ'
  have e1 := hσ' _ (inv f) y J J' hJ gJ'
  have e2 := twist_val hact (inv f) y gJ'
  have e3 := H _ (inv f) y J J' hJ gJ'
  have e4 := hσ _ (inv f ≫ (translT A' θ'.pt).left) y J J' hJ gJ'
  have c : (inv f ≫ (translT A' θ'.pt).left) ≫ f = 𝟙 _ ≫ (translT A θ.pt).left := by
    rw [Category.assoc, ← hT, ← Category.assoc, IsIso.inv_hom_id]
  rw [IsIso.inv_hom_id] at e1 e3
  rw [c] at e4
  rw [e1, e2, e4, e3]
  generalize Ψ (inv f ≫ (translT A' θ'.pt).left) y J J' ^ k = a
  generalize Ψ (inv f) y J J' ^ k = b
  generalize val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ (inv f) y J' = v
  generalize sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ
    (inv f ≫ (translT A' θ'.pt).left) y J' = w
  rw [Units.val_mul, Units.val_mul]
  linear_combination (-(b.val * v.val * w)) * a.mul_inv

end GlobalTheory.ThetaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.HHFibre

open GlobalTheory.ZH GlobalTheory.ZH.RatModel

theorem isHom_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {q : Y.Z ⟶ M.Z}
    (hq : Y.pt ≫ q = M.pt) : M.IsHom Y (AlgHom.id o Ω) q := by
  show Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt
  rw [hq]
  have : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _
    rw [← Spec.map_id]; rfl
  rw [this, Category.id_comp]

theorem exists_pt (X : Scheme.{0}) (w : X) : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X),
    y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply _ _⟩

theorem isUnit_of_isUnit_comap {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω}
    {q : Y.Z ⟶ M.Z} (hq : M.IsHom Y (AlgHom.id o Ω) q) (w : Y.Z) {a : Ω} (ha : a ∈ M.O (q w))
    (ha' : a ∈ Y.O w) (hu : IsUnit (⟨a, ha'⟩ : Y.O w)) : IsUnit (⟨a, ha⟩ : M.O (q w)) := by
  obtain ⟨K, _, y, hy0⟩ := exists_pt Y.Z w
  have hy : Set.range y = {w} := hy0 ▸ range_eq_singleton y (IsLocalRing.closedPoint K)
  have hyq : Set.range (y ≫ q) = {q w} := by
    have := range_eq_singleton (y ≫ q) (IsLocalRing.closedPoint K)
    refine this.trans ?_
    rw [← hy0]
    rfl
  rw [← val_ne_zero_iff hyq]
  rw [← val_ne_zero_iff hy] at hu
  have ha2 : a ∈ M.O (q (y (IsLocalRing.closedPoint K))) := by rw [hy0]; exact ha
  have e := hq.val_comp y (IsLocalRing.closedPoint K) ha2
  simp only [AlgHom.id_apply] at e
  show M.val (y ≫ q) a ≠ 0
  rw [e]
  exact hu

theorem HH_eq_of_hom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M Y : RatModel o Ω)
    (q : Y.Z ⟶ M.Z), Y.pt ≫ q = M.pt → M.HasDiv S.th → ∀ w : Y.Z, S.HH Y w = S.HH M (q w) := by
  intro o Ω _ _ _ S M Y q hq hdiv w
  have hh := isHom_of_pt hq
  unfold ThetaSys.HH
  congr 1
  ext x
  simp only [ThetaSys.supI, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨x₀, h₀⟩ := hdiv (q w)
    have h₀' : Y.Div S.th x₀ w := by simpa using hh.div h₀
    rw [h₀.div_iff_isUnit]
    exact isUnit_of_isUnit_comap hh w _ _ ((h₀'.div_iff_isUnit x).1 hx)
  · intro hx
    simpa using hh.div hx

end GlobalTheory.Poinc.HHFibre
end

