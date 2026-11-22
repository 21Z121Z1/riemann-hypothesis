import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.FormalDegreeBessel.StatementG
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootCong

theorem map_sigR {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem quot_fixed {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : B →+* B) (x Y : Aˣ) (u y y' : B)
    (hx : f x = u * s (f x)) (hy : y = u * s y) (hyy : y * y' = 1) (hY : f (Y⁻¹ : Aˣ) = y') :
    s ((Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) : B) = (Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) := by
  have hs : s y * s y' = 1 := by rw [← map_mul, hyy, map_one]
  change s (f ((x : A) * (Y⁻¹ : Aˣ))) = f ((x : A) * (Y⁻¹ : Aˣ))
  rw [map_mul, hY, map_mul]
  linear_combination (-y') * hx + (s (f x) * s y' * y') * hy - (s (f x) * s y') * hyy
    + (u * s (f x) * y') * hs

theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) :=
  map_sigR _ _ x

theorem exists_idele (D : D7) (y y' : Af D.host.F ⊗[D.host.F] D.host.E) (h : y * y' = 1) :
    ∃ Y : (AE D)ˣ, infPart D (Y : AE D) = 1 ∧ finPart D (Y : AE D) = y ∧
      finPart D ((Y⁻¹ : (AE D)ˣ) : AE D) = y' := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h1 : e.symm (1, y) * e.symm (1, y') = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, h, mul_one]
    exact map_one e.symm
  refine ⟨⟨e.symm (1, y), e.symm (1, y'), h1, by rw [mul_comm, h1]⟩,
    (he _).1.symm.trans ?_, (he _).2.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem exists_idF (D : D7) (b : (Af D.host.F)ˣ) :
    ∃ a : (AF D.host.F)ˣ, finPart D (idF D a : AE D) =
      algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) b := by
  refine ⟨⟨(1, b), (1, (b⁻¹ : (Af D.host.F)ˣ)), Prod.ext (mul_one _) b.mul_inv,
    Prod.ext (mul_one _) b.inv_mul⟩, ?_⟩
  rfl

theorem char_root_eq_one : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (N : ℕ), Odd N → (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1) → ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → (∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) → c x = 1 := by
  intro D V c N hN hF hinf hcong g x hx ⟨w, hw, hwe⟩
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹)) (quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.DetRootCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameterStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_column_operations_model_parameter : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  first | exact @GlobalTheory.FrobStick.det_column_ops | exact GlobalTheory.FrobStick.det_column_ops | (intros; apply GlobalTheory.FrobStick.det_column_ops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
section
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct Matrix RestrictedProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_algebraMap_mem_integers (a : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem eventually_one_tmul_mem_intLoc (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Fv F v) ⊗ₜ[F] e ∈ intLoc F E v := by
  have : Algebra.IsAlgebraic ℤ E := IsFractionRing.comap_isAlgebraic_iff.2 (inferInstance : Algebra.IsAlgebraic ℚ E)
  obtain ⟨d, hd, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) e).exists_integral_multiple
  have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  filter_upwards [eventually_algebraMap_mem_integers (d : F)⁻¹] with v hv
  have h := tmul_mem_intLoc hv (⟨d • e, hi⟩ : 𝓞 E)
  convert h using 1
  change _ = _ ⊗ₜ[F] (d • e)
  rw [← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hd', map_one]

theorem eventually_map_evalV_mem_intLoc (z : Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz => filter_upwards [hy, hz] with v h h' using by rw [map_add]; exact add_mem h h'
  | tmul a e =>
    filter_upwards [a.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a) h (1 : 𝓞 E)) h'
    simpa using this

theorem exists_map_evalV_eq (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v ⊗[F] E)
    (hz : ∀ᶠ v in cofinite, z v ∈ intLoc F E v) :
    ∃ Z : Af F ⊗[F] E, ∀ v, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) Z = z v := by
  let b := Module.finBasis F E
  let c := RingOfIntegers.basis E
  have h1 : ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y ∈ intLoc F E v,
      (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := fun k => by
    filter_upwards [eventually_all.2 fun j => eventually_algebraMap_mem_integers (b.repr (c j : E) k)] with v hv y hy
    refine intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (fun a ha x => ?_) (by simp) (fun y z h h' => by simpa using add_mem h h')
      (fun y h => by simpa using h) hy
    have e : b.repr (x : E) k = ∑ j, c.repr x j • b.repr (c j : E) k := by
      have e' : (x : E) = ∑ j, c.repr x j • (c j : E) := by
        conv_lhs => rw [← c.sum_repr x]
        simp
      simp only [e', map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, e,
      map_sum, map_zsmul]
    exact mul_mem ha (sum_mem fun j _ => zsmul_mem (hv j) _)
  let A : Fin (Module.finrank F E) → Af F := fun k =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (z v) k, by
      filter_upwards [h1 k, hz] with v h h' using h _ h'⟩
  refine ⟨(Algebra.TensorProduct.basis (Af F) b).equivFun.symm A, fun v => ?_⟩
  apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
  ext k
  rw [GlobalTheory.LatticeLocalGlobal.repr_map, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem eventually_one_tmul_mem_latLoc {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L v := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) hx
  | zero => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) L.zero_mem
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with v h h'
    convert add_mem h h' using 1
    funext i
    exact TensorProduct.tmul_add _ _ _
  | smul c x _ hx =>
    filter_upwards [hx, eventually_one_tmul_mem_intLoc (F := F) c] with v h h'
    convert (latLoc F L v).smul_mem ⟨_, h'⟩ h using 1
    funext i
    change _ = (1 : Fv F v) ⊗ₜ[F] c * (1 : Fv F v) ⊗ₜ[F] x i
    simp

theorem eventually_latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v ≤ latLoc F L' v := by
  obtain ⟨s, rfl⟩ := hL
  filter_upwards [(eventually_all_finset s).2 fun x _ => eventually_one_tmul_mem_latLoc (F := F) hL' x] with v hv y hy
  have h1 : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)), (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L' v := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hv x hx
    | zero => exact tmul_mem_latLoc (one_mem _) L'.zero_mem
    | add x y _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      exact TensorProduct.tmul_add _ _ _
    | smul c x _ h =>
      convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc (one_mem _) c⟩ h using 1
      funext i
      change (1 : Fv F v) ⊗ₜ[F] ((c : E) * x i) = (1 : Fv F v) ⊗ₜ[F] (c : E) * (1 : Fv F v) ⊗ₜ[F] x i
      simp
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc ha 1⟩ (h1 x hx) using 1
  funext i
  change _ = a ⊗ₜ[F] ((1 : 𝓞 E) : E) * (1 : Fv F v) ⊗ₜ[F] x i
  simp

variable (F) in

theorem eventually_latLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsLattice E L]
    [hL' : Submodule.IsLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v = latLoc F L' v := by
  filter_upwards [eventually_latLoc_le (F := F) hL.fg hL'.span_eq_top,
    eventually_latLoc_le (F := F) hL'.fg hL.span_eq_top] with v h h' using le_antisymm h h'

omit [NumberField E] in

theorem isLattice_stdLattice : Submodule.IsLattice E (stdLattice E n) := by
  refine ⟨Submodule.fg_pi fun _ => ?_, eq_top_iff.2 fun y _ => ?_⟩
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rw [← Finset.univ_sum_single y]
    refine sum_mem fun i _ => ?_
    have h1 : (Pi.single i 1 : Fin n → E) ∈ stdLattice E n := fun j _ => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
      by_cases e : j = i
      · subst e; simp
      · simp [e]⟩
    convert Submodule.smul_mem _ (y i) (Submodule.subset_span h1) using 1
    rw [← Pi.single_smul, smul_eq_mul, mul_one]

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in
variable {σ J} in

theorem mem_stabLoc_stdLattice_iff {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ J v} :
    k ∈ stabLoc σ J (stdLattice E n) v ↔ (∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J k⁻¹).1 i j ∈ intLoc F E v := by
  have h1 : ∀ k ∈ stabLoc σ J (stdLattice E n) v, ∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v := fun k hk i j => by
    have := mem_latLoc_stdLattice.1 ((mem_stabLoc.1 hk (Pi.single j 1)).1 (mem_latLoc_stdLattice.2 fun l => by
      by_cases e : l = j
      · subst e; simp
      · simp [e])) i
    simpa using this
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y ∈ latLoc F (stdLattice E n) v, M *ᵥ y ∈ latLoc F (stdLattice E n) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  refine ⟨fun hk => ⟨h1 k hk, h1 _ (inv_mem hk)⟩, fun h => mem_stabLoc.2 fun y => ⟨h2 _ h.1 y, fun hy => ?_⟩⟩
  have := h2 _ h.2 _ hy
  rwa [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at this

theorem eventually_stabLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    [Submodule.IsLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, stabLoc σ J L v = stabLoc σ J L' v := by
  filter_upwards [eventually_latLoc_eq F L L'] with v h
  rw [stabLoc, stabLoc, h]

variable (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]

theorem eventually_projFinLoc_mem_stabLoc (g : GFin σ J) :
    ∀ᶠ v in cofinite, projFinLoc σ J v g ∈ stabLoc σ J L v := by
  have := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g).1 i j),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g⁻¹).1 i j)]
    with v h h1 h2
  rw [h, mem_stabLoc_stdLattice_iff, ← map_inv]
  exact ⟨h1, h2⟩

theorem eventually_proj_mem_stabLoc (g : GAd σ J) : ∀ᶠ v in cofinite, proj σ J v g ∈ stabLoc σ J L v := by
  simpa using eventually_projFinLoc_mem_stabLoc σ J L (projFin σ J g)

theorem existsUnique_projFinLoc_eq (x : ∀ v, GLoc σ J v) (hx : ∀ᶠ v in cofinite, x v ∈ stabLoc σ J L v) :
    ∃! g : GFin σ J, ∀ v, projFinLoc σ J v g = x v := by
  refine existsUnique_of_exists_of_unique ?_ fun g h hg hh => GFin_ext σ J fun v => (hg v).trans (hh v).symm
  have := isLattice_stdLattice (E := E) (n := n)
  have h0 : ∀ᶠ v in cofinite, (∀ i j, (matHom _ σ J (x v)).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J (x v)⁻¹).1 i j ∈ intLoc F E v := by
    filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n), hx] with v h h'
    rwa [h, mem_stabLoc_stdLattice_iff] at h'
  choose A hA using fun i j => exists_map_evalV_eq (fun v => (matHom _ σ J (x v)).1 i j) (h0.mono fun v h => h.1 i j)
  choose B hB using fun i j =>
    exists_map_evalV_eq (fun v => (matHom _ σ J (x v)⁻¹).1 i j) (h0.mono fun v h => h.2 i j)
  let φ : ∀ v, Af F ⊗[F] E →+* Fv F v ⊗[F] E := fun v =>
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom
  have hext : ∀ M N : Matrix (Fin n) (Fin n) (Af F ⊗[F] E), (∀ v, M.map (φ v) = N.map (φ v)) → M = N :=
    fun M N h => Matrix.ext fun i j => GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => congrFun₂ (h v) i j
  have hA' : ∀ v, (Matrix.of A).map (φ v) = (matHom _ σ J (x v)).1 := fun v => Matrix.ext fun i j => hA i j v
  have hB' : ∀ v, (Matrix.of B).map (φ v) = (matHom _ σ J (x v)⁻¹).1 := fun v => Matrix.ext fun i j => hB i j v
  have hσ : ∀ v z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (φ v z) = φ v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hJ : ∀ v, (JR (Af F) J).map (φ v) = JR (Fv F v) J := fun v => by ext r s; simp [φ, JR, inclR]
  let u : GL (Fin n) (Af F ⊗[F] E) := ⟨Matrix.of A, Matrix.of B,
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)],
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hu : u ∈ HR (Af F) σ J := hext _ _ fun v => by
    change (cT _ (Matrix.of A) * _ * Matrix.of A).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ _ _ (hσ v), hA', hJ]
    exact (x v).2
  exact ⟨⟨u, hu⟩, fun v => matHom_injective _ σ J (Units.ext (hA' v))⟩

def restrictedEquiv : GFin σ J ≃* Πʳ v, [GLoc σ J v, stabLoc σ J L v] :=
  MulEquiv.ofBijective (F := GFin σ J →* Πʳ v, [GLoc σ J v, stabLoc σ J L v])
    { toFun := fun g => ⟨fun v => projFinLoc σ J v g, eventually_projFinLoc_mem_stabLoc σ J L g⟩
      map_one' := Subtype.ext (funext fun v => map_one (projFinLoc σ J v))
      map_mul' := fun g h => Subtype.ext (funext fun v => map_mul (projFinLoc σ J v) g h) }
    ⟨fun _ _ e => GFin_ext σ J fun v => congrFun (congrArg Subtype.val e) v, fun x =>
      let ⟨g, hg, _⟩ := existsUnique_projFinLoc_eq σ J L x.1 x.2
      ⟨g, Subtype.ext (funext hg)⟩⟩

@[simp] theorem restrictedEquiv_apply (g : GFin σ J) (v : HeightOneSpectrum (𝓞 F)) :
    restrictedEquiv σ J L g v = projFinLoc σ J v g := rfl

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivialStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  first | exact @GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | exact GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | (intros; apply GlobalTheory.LocalUnitaryGlue.exists_finite_adelic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
section
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeOf (D : D7) (ρ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E))

theorem placeOf_bijective (D : D7) : Function.Bijective (placeOf D) := GlobalTheory.CMTypePlaces.places_bijective D

def embOverOf (D : D7) (ρ : D.what₂.Tau) : EmbOver D.host.E (placeOf D ρ) :=
  ⟨tauE D ρ, by
    have := (isCMExt_host D).1
    exact (InfinitePlace.embedding_mk_eq_of_isReal
      (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (placeOf D ρ)))).symm⟩

@[simp] theorem embOverOf_val (D : D7) (ρ : D.what₂.Tau) : (embOverOf D ρ).1 = tauE D ρ := rfl

theorem isInfFam_infProj (D : D7) : IsInfFam (D := D) fun ρ : D.what₂.Tau => infProj (embOverOf D ρ) :=
  fun ρ => isInfEmb_infProj (embOverOf D ρ)

theorem exists_isInfFam (D : D7) : ∃ θ, IsInfFam (D := D) θ := ⟨_, isInfFam_infProj D⟩

variable {D : D7}

theorem eq_placeOf {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) :
    w = placeOf D ρ := by
  rw [placeOf, ← hτ, τ.2, InfinitePlace.mk_embedding]

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem eq_infProj (hθ : IsInfFam θ) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w)
    (hτ : τ.1 = tauE D ρ) : θ ρ = infProj τ :=
  GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hθ ρ) (hτ ▸ isInfEmb_infProj τ)

theorem isAtTau_embArch (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    IsAtTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 (embArch D.sp.cm.sig V.gram w x) := by
  refine ⟨mem_infPts.2 (projFin_embArch _ _ w x), ?_, fun ρ' h => ?_⟩
  · rw [eq_infProj hθ τ hτ, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_self]
  · have hw : placeOf D ρ' ≠ w := fun e => h ((placeOf_bijective D).1 (e.trans (eq_placeOf τ hτ)))
    rw [eq_infProj hθ (embOverOf D ρ') rfl, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_ne _ _ hw,
      map_one]
    rfl

theorem archEquiv_mem_UH (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    (archEquiv V.gram (isCMExt_host D) τ x).1.1 ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  have h := (archEquiv V.gram (isCMExt_host D) τ x).2
  rw [gramAt, ← hτ]
  exact h

theorem exists_archEquiv_eq (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) :
    ∃ x : GArch D.sp.cm.sig V.gram w, (archEquiv V.gram (isCMExt_host D) τ x).1.1 = g := by
  obtain ⟨θ, hθ⟩ := exists_isInfFam D
  obtain ⟨h, hh, -⟩ := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ g hg
  refine ⟨projArch _ _ w h, ?_⟩
  rw [← infMat_infProj, ← eq_infProj hθ τ hτ]
  exact hh.2.1

theorem atTau_archEquiv (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    atTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 = embArch D.sp.cm.sig V.gram w x := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ _ (archEquiv_mem_UH V τ hτ x)
  refine hu.unique ?_ (isAtTau_embArch hθ V τ hτ x)
  unfold atTau
  rw [dif_pos hu.exists]
  exact hu.exists.choose_spec

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRootsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteIdeleChar_at_determinantRoots : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle), (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ) := by
  first | exact @GlobalTheory.DetRootChar.exists_finite_char | exact GlobalTheory.DetRootChar.exists_finite_char | (intros; apply GlobalTheory.DetRootChar.exists_finite_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nthRoot_idele_finitePart_one : ∀ (D : D7) (n : ℕ), 0 < n → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → ∃ y : (AE D)ˣ, y ^ n = x := by
  first | exact @GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one | exact GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one | (intros; apply GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplexStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ) (s : ℂ → ℂ), (∀ j, AlgEnt (f j)) → AlgEnt s → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0 → GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  first | exact @GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | exact GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | (intros; apply GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLogStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_subst_formal_group_log : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → MvPowerSeries.constantCoeff (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ ∀ (c : ℂ_[p]) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p]), GlobalTheory.FrobStick.defect f s = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) (f j) : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) := by
  first | exact @GlobalTheory.FrobStick.SubstLog.subst_log_formula | exact GlobalTheory.FrobStick.SubstLog.subst_log_formula | (intros; apply GlobalTheory.FrobStick.SubstLog.subst_log_formula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x = 1) → ∀ x, c x = 1 := by
  first | exact @GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite | exact GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite | (intros; apply GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite <;> assumption)
end

