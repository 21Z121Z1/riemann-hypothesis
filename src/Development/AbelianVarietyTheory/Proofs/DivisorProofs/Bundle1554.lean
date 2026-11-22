import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurface
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodLatticeActionOfFiniteOrderAutomorphism
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodLattice

variable {P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)}

theorem one_comp_of_isMonHom (f : P.A ⟶ P.A) (hf : IsMonHom f) :
    (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ f = 1 :=
  (IsMonHom.monoidHom f (𝟙_ (Over (Sp ℂ)))).map_one

theorem comp_mul' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (f g : P.A ⟶ P.A) : x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) : x ≫ (1 : P.A ⟶ P.A) = 1 := by
  simp [Hom.one_def]

section Lift

variable (u : HolUnif P.A P.L P.g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem ex_nsmul (k : ℕ) (z : Fin P.g → ℂ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ k ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem lift_unique (f : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u.ex (F' z) = u.ex z ≫ f) : F = F' := by
  have hmem : ∀ z, (F - F') z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h := u.ex_add ((F - F') z) (F' z)
    rw [LinearMap.sub_apply, sub_add_cancel, hF, hF'] at h
    exact mul_eq_right.mp h.symm
  haveI := u.discrete
  let D : (Fin P.g → ℂ) → u.Λ := fun z => ⟨(F - F') z, hmem z⟩
  have hD : Continuous D :=
    Continuous.subtype_mk (LinearMap.continuous_of_finiteDimensional _) _
  refine LinearMap.ext fun z => ?_
  have h1 : D z = D 0 := PreconnectedSpace.constant inferInstance hD
  have h2 : (F - F') z = 0 := by
    have := congrArg Subtype.val h1
    simpa [D] using this
  exact sub_eq_zero.mp (by simpa using h2)

variable (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

def lift (f : P.A ⟶ P.A) (hf : IsMonHom f) : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := Classical.choose (hl f hf)

theorem lift_spec (f : P.A ⟶ P.A) (hf : IsMonHom f) (z) : u.ex (lift u hl f hf z) = u.ex z ≫ f :=
  Classical.choose_spec (hl f hf) z

theorem lift_eq (f : P.A ⟶ P.A) (hf : IsMonHom f) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) : lift u hl f hf = F :=
  lift_unique u f _ _ (lift_spec u hl f hf) hF

theorem lift_mem (f : P.A ⟶ P.A) (hf : IsMonHom f) {z} (hz : z ∈ u.Λ) : lift u hl f hf z ∈ u.Λ := by
  rw [← u.ker] at hz ⊢
  rw [lift_spec, hz, one_comp_of_isMonHom f hf]

def liftZ (f : P.A ⟶ P.A) (hf : IsMonHom f) : Module.End ℤ u.Λ where
  toFun x := ⟨lift u hl f hf x, lift_mem u hl f hf x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_zsmul (lift u hl f hf) c (x : Fin P.g → ℂ))

@[simp] theorem liftZ_val (f : P.A ⟶ P.A) (hf : IsMonHom f) (x : u.Λ) :
    ((liftZ u hl f hf x : u.Λ) : Fin P.g → ℂ) = lift u hl f hf x := rfl

end Lift

section Ring

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)
  {O : Type} [CommRing O] (act : OAct O P.A)

theorem act_zero : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ringAct : O →+* Module.End ℤ u.Λ where
  toFun c := liftZ u hl (act.act c) (act.hom c)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.one_apply]
    rw [lift_eq u hl _ _ LinearMap.id (fun z => by rw [act.one, Category.comp_id]; rfl)]
    rfl
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.mul_apply]
    rw [lift_eq u hl _ _ ((lift u hl (act.act a) (act.hom a)).comp (lift u hl (act.act b) (act.hom b)))
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, ← act.mul, mul_comm])]
    rfl
  map_zero' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [lift_eq u hl _ _ 0 (fun z => by rw [LinearMap.zero_apply, ex_zero, act_zero, comp_one'])]
    rfl
  map_add' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.add_apply, Submodule.coe_add]
    rw [lift_eq u hl _ _ (lift u hl (act.act a) (act.hom a) + lift u hl (act.act b) (act.hom b))
      (fun z => by rw [LinearMap.add_apply, u.ex_add, lift_spec, lift_spec, act.add, comp_mul'])]
    rfl

@[simp] theorem ringAct_val (c : O) (x : u.Λ) :
    ((ringAct u hl act c x : u.Λ) : Fin P.g → ℂ) = lift u hl (act.act c) (act.hom c) x := rfl

end Ring

section Main

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

theorem lift_pow_spec (θ : P.A ⟶ P.A) (hθ : IsMonHom θ) (k : ℕ) (z : Fin P.g → ℂ) :
    u.ex ((lift u hl θ hθ ^ k) z) = u.ex z ≫ (fun f : P.A ⟶ P.A => f ≫ θ)^[k] (𝟙 P.A) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply, Function.iterate_zero, id, Category.comp_id]
  | succ k ih => rw [pow_succ', Module.End.mul_apply, lift_spec, ih, Function.iterate_succ_apply', Category.assoc]

include u hl in
theorem main_of_unif (E : Type) [Field E] [NumberField E] (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ)
    (hθ : IsMonHom θ) (hN : (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A)
    (hc : ∀ a, act.act a ≫ θ = θ ≫ act.act a) (hn : 0 < n) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)),
      Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
      (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧
      (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  letI inst : Module (𝓞 E) u.Λ := Module.compHom u.Λ (ringAct u hl act)
  have hsmul : ∀ (c : 𝓞 E) (x : u.Λ), ((c • x : u.Λ) : Fin P.g → ℂ) = lift u hl (act.act c) (act.hom c) x :=
    fun _ _ => rfl

  have hcomm : ∀ c, (lift u hl θ hθ).comp (lift u hl (act.act c) (act.hom c)) =
      (lift u hl (act.act c) (act.hom c)).comp (lift u hl θ hθ) := fun c =>
    lift_unique u (act.act c ≫ θ) _ _
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, hc])
  let F : u.Λ →ₗ[𝓞 E] u.Λ :=
    { toFun := liftZ u hl θ hθ
      map_add' := map_add _
      map_smul' := fun c x => Subtype.ext (by
        simp only [RingHom.id_apply, hsmul, liftZ_val]
        exact (LinearMap.congr_fun (hcomm c) x : _)) }
  have hFval : ∀ x : u.Λ, ((F x : u.Λ) : Fin P.g → ℂ) = lift u hl θ hθ x := fun _ => rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let ψ : u.Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun a => u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))
  have hψlift : ∀ (f : P.A ⟶ P.A) (hf : IsMonHom f) (a : u.Λ),
      u.ex ((n : ℂ)⁻¹ • lift u hl f hf a) = ψ a ≫ f := fun f hf a => by
    rw [← map_smul, lift_spec]
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI hZ : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  refine ⟨u.Λ, inferInstance, inst, F, ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) u.Λ
  · refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    right
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have hm : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc0
    have h1 : (Ideal.absNorm (Ideal.span {c}) : 𝓞 E) • x = 0 := by
      rw [← hr, mul_smul, h, smul_zero]
    rw [Nat.cast_smul_eq_nsmul] at h1
    have h2 := congrArg Subtype.val h1
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact Subtype.ext ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm))
  · have hpow : lift u hl θ hθ ^ N = 1 := by
      rw [lift_unique u (𝟙 P.A) (lift u hl θ hθ ^ N) 1
        (fun z => by rw [lift_pow_spec, hN]) (fun z => by rw [Module.End.one_apply, Category.comp_id])]
    have hit : ∀ (k : ℕ) (x : u.Λ), (((F ^ k) x : u.Λ) : Fin P.g → ℂ) = (lift u hl θ hθ ^ k) x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, hFval, ih, pow_succ', Module.End.mul_apply]
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [hit, hpow]; rfl
  · intro a b
    simp only [ψ, Submodule.coe_add, smul_add, u.ex_add]
  · intro c a
    simp only [ψ]
    rw [hsmul, hψlift]
  · intro a
    simp only [ψ]
    rw [u.ker]
    constructor
    · intro h
      refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hn']
    · rintro ⟨b, rfl⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hn']
      exact b.2
  · intro q hq
    obtain ⟨z, rfl⟩ := u.ex_onto q
    have hz : (n : ℂ) • z ∈ u.Λ := by
      rw [← u.ker, Nat.cast_smul_eq_nsmul, ex_nsmul, hq]
    refine ⟨⟨_, hz⟩, ?_⟩
    simp only [ψ]
    rw [inv_smul_smul₀ hn']
  · intro a
    simp only [ψ]
    rw [hFval, hψlift]

end Main

end GlobalTheory.PeriodLattice

theorem GlobalTheory.periodLattice_of_finiteOrder : ∀ (E : Type) [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ), IsMonHom θ → 0 < N → (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A → (∀ a, act.act a ≫ θ = θ ≫ act.act a) → 0 < n → ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧ (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  intro E _ _ P act θ N n hθ _ hN hc hn
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, -, -, -, -, -, -, -, hl, -⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  exact GlobalTheory.PeriodLattice.main_of_unif u hl E act θ N n hθ hN hc hn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhRatOfSerCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhRatCommon

set_option maxHeartbeats 1000000 in

theorem phRat_of_ser_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∀ cc, SerOf (O i) (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ x : (O i).Cl' () → VsV D i (O i).c'.F, ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) (O i).c' ((O i).dδ ()) ((O i).w ()) ((O i).La ()) ((O i).Nc ()) ((O i).gam ()) ((O i).vol ()) ((O i).ep ()) (O i).io x f) → (O i).EquivAt (κ i) cc → (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR t O i hpins cc hser hex hequiv
  obtain ⟨hcc, hph, hs⟩ := hser
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (t.kap i τ).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  refine GlobalTheory.PhaseRationalDegenerate.of_before_projector (O i) (κ i) _ cc hequiv hR.grp.chiW hR.thP.thG 1 fun x₀ => ?_
  obtain ⟨h, J', hrep, hP, -, -⟩ := (hpins.2.tuple ()).reps
  obtain ⟨x, hx⟩ := hP x₀
  obtain ⟨f, hf, hcl⟩ := hex x
  have hf' : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n := by
    rw [hn]; exact hf
  have hBC := exists_rdU_eq_sum (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') _ _ f hf'
  obtain ⟨m, as, fs, hbc⟩ := hBC
  have hL : ∀ a : (O i).c'.F, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' a := fun a => by
    have : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hpins.1 ▸ a.2
    exact this
  choose b hb using hL
  refine ⟨m, fun j => b (as j), fs, fun g => ?_⟩
  have := hs () h J' hrep _ x hx f hf.1 hcl g
  have e1 := hbc ((O i).dict g).1 ((O i).dict g).2
  have e2 : ∀ j, (O i).phi cc (fs j : T.R ((i : ℕ) + 1)) g = cc ((O i).dict g).1 * (O i).mu g *
      rdU (T.U ((i : ℕ) + 1) (O i).s0) (fs j : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := fun j => rfl
  exact this.trans (sum_shape e1 (fun j => hb (as j)) e2)

end GlobalTheory.PhRatCommon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.PullbackFinitePoint

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔ (f.residueFieldMap x).hom.Finite := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  unfold Scheme.Hom.residueDegree RingHom.Finite
  constructor
  · intro h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  · intro h
    exact Module.finrank_pos.ne'

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private theorem residueFieldMap_surjective_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap, ConcreteCategory.comp_apply]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : f.residueDegree x ≠ 0 :=
  (_root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite f x).2
    (RingHom.Finite.of_surjective _ (residueFieldMap_surjective_of_surjectiveOnStalks f x))

theorem residueDegree_SpecMap_ne_zero {K : CommRingCat.{0}} {L : Type} [Field L]
    (φ : K ⟶ CommRingCat.of L) (hφ : φ.hom.Finite) (q : Spec (CommRingCat.of L)) :
    (Spec.map φ).residueDegree q ≠ 0 := by
  rw [residueDegree_ne_zero_iff_finite]
  have hb : Function.Surjective
      ((Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation q).hom := by
    have : Subsingleton (Spec (CommRingCat.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
    intro a
    obtain ⟨b, rfl⟩ := (Spec (.of L)).residue_surjective _ a
    obtain ⟨U, hU, c, rfl⟩ := (Spec (.of L)).presheaf.exists_germ_eq b
    obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => Subsingleton.elim q y ▸ hU
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of L)).inv).2 c
    exact ⟨r, rfl⟩
  have e : ((Scheme.ΓSpecIso K).inv ≫ (Spec K).Γevaluation (Spec.map φ q)) ≫
      (Spec.map φ).residueFieldMap q =
      φ ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation q := by
    rw [Category.assoc, Scheme.Γevaluation_naturality, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have h := (RingHom.Finite.of_surjective _ hb).comp hφ
  rw [← CommRingCat.hom_comp, ← e, CommRingCat.hom_comp] at h
  exact h.of_comp_finite

theorem residueDegree_ne_zero_of_fieldPoint {P Y : Scheme.{0}} {L : Type} [Field L]
    (w : Spec (CommRingCat.of L) ⟶ P) (π : P ⟶ Y) (y : Y)
    (φ : Y.residueField y ⟶ CommRingCat.of L) (hφ : φ.hom.Finite)
    (h : w ≫ π = Spec.map φ ≫ Y.fromSpecResidueField y) (q : Spec (CommRingCat.of L)) :
    π.residueDegree (w q) ≠ 0 := by
  have h₁ := CurveDegreesCompare.residueDegree_comp w π q
  rw [h, CurveDegreesCompare.residueDegree_comp] at h₁
  have h₂ := mul_ne_zero (residueDegree_ne_zero_of_surjectiveOnStalks
    (Y.fromSpecResidueField y) (Spec.map φ q)) (residueDegree_SpecMap_ne_zero φ hφ q)
  rw [h₁] at h₂
  exact left_ne_zero_of_mul h₂

theorem exists_point : ∀ (X Y₁ Y₂ : Scheme.{0}) (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (y₁ : Y₁) (y₂ : Y₂),
    f y₁ = g y₂ → f.residueDegree y₁ ≠ 0 → g.residueDegree y₂ ≠ 0 →
    ∃ z : ↥(Limits.pullback f g), (Limits.pullback.fst f g) z = y₁ ∧
      (Limits.pullback.snd f g) z = y₂ ∧ (Limits.pullback.fst f g).residueDegree z ≠ 0 ∧
      (Limits.pullback.snd f g).residueDegree z ≠ 0 := by
  intro X Y₁ Y₂ f g y₁ y₂ h h₁ h₂
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.mk' y₁ y₂ h
  have hf : ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.Finite :=
    ((residueDegree_ne_zero_iff_finite f y₁).1 h₁).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hx).inv).2)
  have hg : ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite :=
    ((residueDegree_ne_zero_iff_finite g y₂).1 h₂).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hy).inv).2)
  have hl : T.tensorInl.hom.Finite :=
    RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg
  have hr : T.tensorInr.hom.Finite := by
    have h₃ := RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso
      ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) _ hf
    have h₄ := (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Limits.pushoutSymmetry ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
        ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)).hom).2).comp h₃
    have e := Limits.inl_comp_pushoutSymmetry_hom
      ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
      ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    exact congr($(e).hom.Finite) ▸ h₄
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T.tensor
  letI := Ideal.Quotient.field m
  let ρ : T.tensor ⟶ CommRingCat.of (T.tensor ⧸ m) := CommRingCat.ofHom (Ideal.Quotient.mk m)
  have hρ : ρ.hom.Finite := RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  let q : Spec (CommRingCat.of (T.tensor ⧸ m)) := (⊥ : PrimeSpectrum (T.tensor ⧸ m))
  refine ⟨(Spec.map ρ ≫ T.SpecTensorTo) q, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply]
    exact T.fst_SpecTensorTo_apply _
  · rw [Scheme.Hom.comp_apply]
    exact T.snd_SpecTensorTo_apply _
  · refine residueDegree_ne_zero_of_fieldPoint _ _ T.x (T.tensorInl ≫ ρ) (hρ.comp hl) ?_ q
    rw [Category.assoc, T.specTensorTo_fst, Spec.map_comp, Category.assoc]
  · refine residueDegree_ne_zero_of_fieldPoint _ _ T.y (T.tensorInr ≫ ρ) (hρ.comp hr) ?_ q
    rw [Category.assoc, T.specTensorTo_snd, Spec.map_comp, Category.assoc]

end GlobalTheory.PullbackFinitePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GaloisLBDescent

theorem lbIso_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ _ φ₁ φ PA PB L' hA hG h₁ h hL' i₁ i₂
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hPA := PA.isLB
  have h₂ := pull_isLB PB.isLB φ
  have hN := LB.isLB_div h₂ hPA
  have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ PB.isLB) - CechPic.cls _ hPA :=
    CechPic.cls_div h₂ hPA hN
  have zA : CechPic.pull (eSec A) (CechPic.cls _ PA.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PA.isLB _)).2 ⟨_, PA.rigGen⟩
  have zB : CechPic.pull (eSec B) (CechPic.cls _ PB.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PB.isLB _)).2 ⟨_, PB.rigGen⟩
  have c₁ : CechPic.cls _ hL' = CechPic.pull φ₁ (CechPic.cls _ PA.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PA.isLB _)).2 i₁
  have c₂ : CechPic.cls _ hL' = CechPic.pull (φ₁ ≫ φ) (CechPic.cls _ PB.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PB.isLB _)).2 i₂
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns S S₁ π₁ A _ hA hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · have he : eSec A ≫ φ = f ≫ eSec B := GlobalTheory.PolBaseChange.eSec_comm h
    rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, zA, he, CechPic.pull_comp, zB, map_zero,
      sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← h₁.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub,
      ← CechPic.pull_comp φ₁ φ, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.GaloisLBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionThetaStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_adapted_pair_restriction_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ) := by
  first | exact @GlobalTheory.MixedLagr.exists_ratLagr | exact GlobalTheory.MixedLagr.exists_ratLagr | (intros; apply GlobalTheory.MixedLagr.exists_ratLagr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurfaceStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface : SlopeBound := by
  first | exact @GlobalTheory.HSShort.SlopeTop.slopeBound | exact GlobalTheory.HSShort.SlopeTop.slopeBound | (intros; apply GlobalTheory.HSShort.SlopeTop.slopeBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCommutesMajorantStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_commutes_majorant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsLattice E →
    ∀ g : GAd σ X.Jᵀ, GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X →
      (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) ∧
      ∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v := by
  first | exact @GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK | exact GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK | (intros; apply GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBoundStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supremum_constant_log_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ), 2 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 1 ≤ w → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log w ≤ 2 * L → 1 ≤ supConst E r d M w ∧ Real.log (supConst E r d M w) ≤ 250 * (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L := by
  first | exact @GlobalTheory.SupConstSize.supConst_size | exact GlobalTheory.SupConstSize.supConst_size | (intros; apply GlobalTheory.SupConstSize.supConst_size <;> assumption)
end

