import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutEnd2Ao
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.TnOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BFixOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdmissibleRankTwoSelf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
namespace UpperTheory.GalN.V
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
variable {D : Dat Ω K c e ψ} {ι : Qbar l ≃+* ℂ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
theorem mod0'_alt (h : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) : ∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) := h.1
theorem witAQ_of_isModularA (_ : _root_.UpperTheory.V.Af.Hypotheses') (_ : Continuous W) (_ : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) (_ : 1 ≤ e)
    (h : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) : _root_.UpperTheory.V.Z.Win.WitAQ ι W := h.2
end
theorem adm2B_of_adm2B (_ : _root_.UpperTheory.V.Af.Hypotheses') (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (_ : l ≠ 2) (ι : Qbar l ≃+* ℂ) (e M : ℕ) (_ : 1 ≤ e) (ρ : G K Ω →* GL (Fin 3) (Qbar l))
    (h : _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M ρ) : _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M ρ := h
end UpperTheory.GalN.V
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Af
open UpperTheory.V.Published
structure HypothesesH' : Prop extends toClassicalTheorems : _root_.UpperTheory.V.Af.Hypotheses' where
  descU : Z.Desc.DescWeak
  cyc : Z.Bc.CycC
  cyc2 : Z.Bc.Desc2
  quat : DefQuatExists
  ssR : CuspSemisimpleReal
def AutBridgeAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)),
    (∀ [IsTotallyReal F], IsAut ι r ↔ IsAutR ι r) ∧
    (∀ [IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π) ∧
    ∀ [IsCMField F], _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r → IsAut ι r
section Ver
variable {F L Ω : Type} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
  {C : Type} [CommGroup C]
end Ver
section Compat
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
end Compat
end UpperTheory.V.Af
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfLevelIso
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Af
section Rep
variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
end Rep
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {r r' : G F Ω →* GL (Fin n) (Qbar l)}
variable [IsAlgClosure F Ω]
abbrev _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty : Prop := ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (P : _root_.UpperTheory.V.Af.Hypotheses') {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w),
    ∃ rc : IrrGL (w.adicCompletion F) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc
end UpperTheory.V.Af
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AlgNormDiag
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.CuspRep Polynomial
open UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem root_diag {n : ℕ} (α : Fin n → ℂˣ) (y : WD h)
    (e : y = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2))) (φ : ↥(Weil h)) (hd : deg φ = 1) (z : ℂ)
    (hz : (WD.charPol y φ).IsRoot z) : ∃ b ∈ algSat n (normV w) (Finset.univ.val.map α), z * b = 1 := by
  subst e
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd] at hz
  rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, -, hi⟩ := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, zpow_one] at hi
  have hq : (((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) * ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = 1 := by
    have h0 : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (by omega : (normV w : ℕ) ≠ 0)
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_add _ _ h0]
    have : ((((1 : ℝ) - n) / 2 : ℝ) : ℂ) + ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [this, Complex.cpow_zero]
  refine ⟨((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α i : ℂ), ?_, ?_⟩
  · rw [algSat, Multiset.mem_map]
    refine ⟨(α i : ℂ), ?_, rfl⟩
    simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map]
    exact Multiset.mem_map_of_mem (fun j => ((α j : ℂˣ) : ℂ)) (Finset.mem_univ i)
  · rw [hi]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_qPow]
    have ha : (α i : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    exact hq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.CuspRep.ParLaws in
private theorem algNorm_diag {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (w.adicCompletion E) → WD h} (L : LawsT a ha rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) n
    ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ (GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL hB)
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have hx : GlobalTheory.SmGL.HasSatake (IrrGL.of σ.ρ σ.smooth σ.irred).rep α :=
    ⟨(IrrGL.of σ.ρ σ.smooth σ.irred).2.rep.irr, fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hα.2.1,
      (IsSubquotient.of_surjective (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toIntertwiningMap (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toLinearEquiv.surjective).trans hα.2.2⟩
  have e := GlobalTheory.RecT.SphLaw.sat ((GlobalTheory.RecT.lawsT_iff a ha rc).2 L) (IrrGL.of σ.ρ σ.smooth σ.irred) α hx
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
  change (_ : ℂ) * ((_ : ℂ) * v i) = _ * (_ * v i)
  ring
end UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.recFrob_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → RecFrob := by
  intro _ E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ B _ hB φ hd z hz
  obtain ⟨α, rfl, e⟩ := algNorm_diag L σ B hB
  exact root_diag α _ e φ hd z hz
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut
namespace UpperTheory.V.Pr
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
section Ord
variable (l : ℕ) {O : Type} [CommRing O] [IsLocalRing O] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω)
  (B : ValuationSubring Ω)
end Ord
variable {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω)
def AutEnd3Alt (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A),
    OrdPt l η Ψ σ g₁ B r →
    (∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val r))) →
    ∀ [Algebra K Ω] (ρ : G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)).mat) →
      _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw ρ (cycBar K Ω l)⁻¹)
def HostEndAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ →
  ∀ σ : G ℚ Ω, IsCC σ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
  ∃ g₁, Marks (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ ∧
    FinEnd l (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B ∧
    _root_.UpperTheory.V.Pr.AutEnd3Alt c (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B K ι
def GdEndAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ)
    (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 →
  ∃ g₁, Marks D.η D.Ψ D.cc g₁ ∧ FinEnd l D.η D.Ψ D.cc g₁ B ∧ _root_.UpperTheory.V.Pr.AutEnd3Alt c D.η D.Ψ D.cc g₁ B K ι ∧
    _root_.UpperTheory.V.Z.Win.Dn.AutEnd2Ao c D.η D.Ψ D.cc g₁ B e ι
end UpperTheory.V.Pr
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.COpenEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.J
open UpperTheory.V.Pr
theorem mod_l_open_existence
    {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {c : Coef l}
    [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} (H : LinkHyp c N e η σ B M)
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
    {k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ} (v : Φ.V)
    {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
    {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (Λ : W.LamObj R.r)
    (hΛ : Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin (n * Module.finrank ℚ (W.Lp L))) c₁.O))
    (J : Ideal R.B₀.B) (hJ : R.B₀.ModularAlt ι J Λ) (hs : R.T.IdealSpecializationPoint J) : R.T.ModIn J := by
  obtain ⟨hd, -⟩ := degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v
  refine ⟨⟨Λ, hJ.ring.fin⟩, ?_, fun g hg => (hJ.ring.unr0 R.v0 g hg).1,
    n4Of Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f n ka R, hJ.p1, hJ.p3, hs⟩
  intro Z hZ
  haveI : IsDiscreteValuationRing c₁.O := c₁.dvr
  have := dimOf c₁.O Λ.Λ R.B₀.B (Λ.toPair R.B₀.u : Λ.Λ →+* R.B₀.B) J _ hΛ hJ.ring.fin hJ.ring.tf Z hZ
  rw [← hd] at this
  exact this
end UpperTheory.V.J
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuDefsA
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix
namespace UpperTheory.V.Cu
section Alg
variable {R : Type} [CommRing R]
end Alg
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def TauExAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (K' : IntermediateField ℚ Ω) [NumberField K'], l ≠ 2 → Module.finrank ℚ K' = 2 → IsTotallyComplex K' → ¬ (l : ℤ) ∣ discr K' →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup) → (∃ cc : G ℚ Ω, Sd.IsCC cc) →
    ∀ g0 ∉ K'.fixingSubgroup, ∃ (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ), ∀ c₂ : Coef l, c₁.O ≤ c₂.O → ∀ j : ℕ, 1 ≤ j →
      ∃ τ s, TauDat ι K' g0 (m * j) c₂ τ s (κ ^ j)
end UpperTheory.V.Cu
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndPtOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th
open private det_comap tw_flag unramified_at_base_place irr_of_mat pt_flag w_ne from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NiceAt
namespace UpperTheory.Gal.projectedFormsSystemPart
private theorem la_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A A' : ValuationSubring Ω} {w w' : W.Plc F} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (e : A = A')
    (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (ψ' : Fin n → Dec (F := F) A' →* (Qbar l)ˣ)
    (hψ : ∀ j (g : Dec (F := F) A) (g' : Dec (F := F) A'), (g : G F Ω) = (g' : G F Ω) → ψ j g = ψ' j g') (wt : Fin n → W.Emb l w → ℤ)
    (hm : ∀ τ, StrictMono fun j => wt j τ) (hl : ∀ j, W.IsLocAlg h (ψ j) (wt j)) :
    ∃ wt' : Fin n → W.Emb l w' → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧ ∀ j, W.IsLocAlg h' (ψ' j) (wt' j) := by
  subst e
  obtain rfl : w = w' := IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))
  obtain rfl : ψ = ψ' := funext fun j => MonoidHom.ext fun g => hψ j g g rfl
  exact ⟨wt, hm, hl⟩
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}
def EndPtAlt (R : CReal k c₁ f 3 ka) (ι : Qbar l ≃+* ℂ) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) : Prop :=
  ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
    ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Arith h → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr)
private theorem psi_eq (R : CReal k c₁ f 3 ka) {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ) (ξ : R.S.A →ₐ[c₁.O] Qbar l) (v) :
    W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R.B₀) ((ξ.comp R.S.inc).comp φ) v = R.K.twψ (ptRep R.S ξ) v :=
  funext fun i => (TwLink.IsPhi.maps R.K hφ ξ).2 v i
private theorem off_self (R : CReal k c₁ f 3 ka) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ)
    {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J) (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l)
    (hV : VPt R.S ξ) (hTI : R.S.u.TI (RingHom.ker ξ)) (ha : W.UniversalOrdinaryDeterminantRing.Pt.Arith (B := R.B₀) ((ξ.comp R.S.inc).comp φ) h) :
    _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN R.s.v0 ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr) := by
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D (B := R.B₀) ((ξ.comp R.S.inc).comp φ) = W.GDet.ofRep (R.K.tw (ptRep R.S ξ)) :=
    (TwLink.IsPhi.maps R.K hφ ξ).1
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep (B := R.B₀) ((ξ.comp R.S.inc).comp φ) ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr) := by
    refine (congrArg (fun D : W.GDet 3 (Qbar l) R.V.frame.G₀ => D.comap R.V.pr) hD).trans
      (det_comap (R.K.tw (ptRep R.S ξ)) R.V.pr (W.mat ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr)) fun g => rfl)
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN R.v0 hE ((ξ.comp R.S.inc).comp φ) h _
    (fun b hb => hg _ (RingHom.ker_isPrime _) hTI (Ideal.mem_map_of_mem φ hb)) ha hrep
    (irr_of_mat _ R.V.pr (Pr.pr_surj R.V) (R.K.tw_irr _ (irrTI l c₁ _ R.C₀ 3 R.ok (Or.inr rfl) R.S ξ hV.1 hTI)))
private theorem kap (R : CReal k c₁ f 3 ka) (g : G L Ω) : R.K.κA (Qbar l) (R.V.pr g) = ka g := Units.ext (R.κ_pr g)
private theorem psi_j (ρ : Fr.NRep (Φ.ext f) 3 (Qbar l)) {u u' : Φ.V} (e : u = u') (j : Fin 3) (a : Φ.Gv u) (a' : Φ.Gv u')
    (h : (k.j u a).1 = (k.j u' a').1) : ρ.ψ u j a = ρ.ψ u' j a' := by
  subst e
  rw [k.j_inj u (Subtype.ext h)]
theorem endPt_of_allGood_of_arithmeticPointClassicality (R R₀ : CReal k c₁ f 3 ka) (hp : ¬ R₀.s.p ∣ R.s.p) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B}
    (hφ : R.T.IsPhi φ) {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J)
    {φ' : R₀.B₀.B →ₐ[c₁.O] R.S.B} (hφ' : (setS R₀ R.S).T.IsPhi φ') {J' : Ideal R₀.B₀.B} (hg' : AllGood R.S (J'.map φ'))
    (hE' : R₀.B₀.arithmeticPointClassicalityDense ι J') : _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ := by
  rintro h ξ hV hTI _ rfl ha
  have key : ∀ v' : W.Vl l L, ∃ wt' : Fin 3 → W.Emb l (R₀.s.w v') → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧
      ∀ j, W.IsLocAlg (R₀.s.hw v') (W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R₀.B₀) ((ξ.comp R.S.inc).comp φ') v' j) (wt' j) := fun v' => by
    obtain ⟨v, hv⟩ : ∃ v : W.Vl l L, R.K.e v = R₀.K.e v' := R.K.e.surjective (R₀.K.e v')
    refine la_move (R.s.hw v) (R₀.s.hw v') ((R.A_pl v).trans ((congrArg k.pl hv).trans (R₀.A_pl v').symm)) _ _
      (fun j g g' e => ?_) (h v) (ha.1 v) (ha.2 v)
    rw [psi_eq R hφ ξ v, psi_eq (setS R₀ R.S) hφ' ξ v']
    change (ptRep R.S ξ).ψ (R.K.e v) j (R.K.lam v g) * R.K.κA (Qbar l) (R.V.pr g) =
      (ptRep R.S ξ).ψ (R₀.K.e v') j (R₀.K.lam v' g') * R₀.K.κA (Qbar l) (R₀.V.pr g')
    rw [kap, kap, e]
    exact congrArg (· * ka g') (psi_j (k := k) (ptRep R.S ξ) hv j (R.K.lam v g) (R₀.K.lam v' g')
      ((R.lam_j v g).trans ((congrArg (galEmb ℚ L Ω) e).trans (R₀.lam_j v' g').symm)))
  choose wt' h1 h2 using key
  have a := off_self R hφ hg hE h ξ hV hTI ha
  have b := off_self (setS R₀ R.S) hφ' hg' hE' wt' ξ hV hTI ⟨h1, h2⟩
  have e : ((setS R₀ R.S).K.tw (ptRep R.S ξ)).toHomUnits.comp (setS R₀ R.S).V.pr =
      (R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr := MonoidHom.ext fun g => Units.ext (by
    change ((R₀.K.κA (Qbar l) (R₀.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R₀.K.π (R₀.V.pr g)) =
      ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R.K.π (R.V.pr g))
    rw [kap, kap, R.π_pr, R₀.π_pr])
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (v0_ne hp) a (e ▸ b)
end
theorem niceAt2_alt :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ →
      R.S.u.TI (RingHom.ker ξ) → ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Good h →
      (Th.Free R.V.frame fun v => x.psi v) →
      _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x (R.K.tw (ptRep R.S ξ)).toHomUnits ∧ ∀ v, x.psi v = R.K.twψ (ptRep R.S ξ) v := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f ka R _ _ φ hφ hJ h ξ hV hTI x hx hGood hFree
  have hn : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3 := Or.inr rfl
  let ρQ : Fr.NRep (Φ.ext f) 3 (Qbar l) := ptRep R.S ξ
  let ρ0 : R.V.frame.G₀ →* GL (Fin 3) (Qbar l) := (R.K.tw ρQ).toHomUnits
  have hm : R.B₀.u.Maps ((ξ.comp (R.S.inc.comp φ) : R.B₀.B →ₐ[c₁.O] Qbar l) : R.B₀.B →+* Qbar l)
      (W.GDet.ofRep (R.K.tw ρQ)) (R.K.twψ ρQ) := TwLink.IsPhi.maps R.K hφ ξ
  have hxe : x = ξ.comp (R.S.inc.comp φ) := hx
  have hψ : ∀ v, x.psi v = R.K.twψ ρQ v := fun v => funext fun i => by
    rw [hxe]
    exact hm.2 v i
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D x = W.GDet.ofRep (R.K.tw ρQ) := by
    rw [hxe]
    exact hm.1
  have hcont : Continuous ρ0 := by
    have h1 : Continuous (R.K.tw ρQ) := by
      refine continuous_matrix fun a b => ?_
      have h2 := continuous_subtype_val.comp (((X.So.adicCont l c₁).2 _ _).1 R.K.κ_cont)
      have h3 := ((derRep l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 0 (Submodule.zero_mem _)).1 a b).comp R.K.π_cont
      exact h2.mul h3
    exact Units.continuous_iff.2 ⟨h1, h1.comp continuous_inv⟩
  have hirr : MatIrr ⊤ (W.mat ρ0) := R.K.tw_irr ρQ (irrTI l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 hTI)
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep x (ρ0.comp R.V.pr) := by
    refine (congrArg (fun D => D.comap R.V.pr) hD).trans (det_comap (R.K.tw ρQ) R.V.pr (W.mat (ρ0.comp R.V.pr)) fun g => rfl)
  have harith : W.UniversalOrdinaryDeterminantRing.Pt.Arith x h := ⟨hGood.1, fun v j => by
    obtain ⟨ph, hph, -⟩ := hGood.2 v
    exact ⟨ph j, hph j⟩⟩
  have hA : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ0 := by
    refine ⟨hcont, hrep, ⟨h, harith⟩, hJ h ξ hV hTI x hx harith, ?_, fun v => ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      have h1 : R.K.π (R.V.pr g) = 1 := by
        rw [R.π_pr]
        exact unramified_at_base_place e ψ H.dvd k _ R.v0M g hg
      have h2 : R.K.κ (R.V.pr g) = 1 := R.K.ramκ _ ⟨g, hg, rfl⟩
      refine Units.ext ?_
      change ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • ρQ.r (R.K.π (R.V.pr g)) = 1
      have h3 : ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) = 1 := by
        change algebraMap c₁.O (Qbar l) ((R.K.κ (R.V.pr g) : (↥c₁.O)ˣ) : c₁.O) = 1
        rw [h2, Units.val_one, map_one]
      rw [h1, map_one, h3, one_smul]
    · rw [hψ v]
      obtain ⟨g₀, hg⟩ := R.ok.f3 (R.K.e v)
      exact tw_flag R.K ρQ v (pt_flag R.S ξ hV hn _ g₀ hg)
  have hVne : Nonempty Φ.V := by
    by_contra hV'
    rw [not_nonempty_iff] at hV'
    have h' : _ < Φ.d := R.big.1
    simp [Fr.Frame.d] at h'
  obtain ⟨v'⟩ := hVne
  refine ⟨_root_.UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free ι x ρ0 hn hA hirr hFree ?_, hψ⟩
  obtain ⟨v, hv⟩ := R.K.e.surjective v'
  obtain ⟨s, hs⟩ := R.ok.f3 (R.K.e v)
  obtain ⟨g, rfl⟩ := (R.K.lam v).surjective s
  refine ⟨v, 0, 1, g, fun h' => w_ne hn _ hs 0 1 (by decide) ?_⟩
  rw [R.K.psib, R.K.psib, R.K.chib, R.K.chib, ← R.K.lam_loc] at h'
  exact mul_right_cancel h'
def Red2Alt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → Function.Surjective φ → ∀ J, AllGood R.S (J.map φ) → R.T.DimT J → R.B₀.Dense J →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ ξ : R.S.A →ₐ[c₁.O] Qbar l, IntPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
      ∀ a ∈ J, ∃ s : R.S.A, ξ s ≠ 0 ∧ s * R.S.inc (φ a) = 0
theorem red2_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.V.Th.DenseThresholdMainCase → _root_.UpperTheory.Gal.projectedFormsSystemPart.Red2Alt := by
  intro hG hC Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f ka R hW hK φ hPhi hSurj J hAll hDim hDense hEnd ξ hξ hTI a ha
  obtain ⟨h, hInc, hFree⟩ := wtEx hG Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hNice := _root_.UpperTheory.Gal.projectedFormsSystemPart.niceAt2_alt Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK φ hPhi hEnd h
  have hFix := _root_.UpperTheory.V.J.fixOf_alt hC Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hN : IsNoetherianRing R.B₀.B := IsCO.toIsNoetherian (O := c₁.O)
  have hD : DenseB R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) :=
    @denseOf l _ c₁ R.B₀.B R.S.B _ hN _ _ _ φ J (1 + 3 * (Φ.ext f).d) (fun x => W.UniversalOrdinaryDeterminantRing.Pt.Good x h) hSurj hDim (hDense h hInc)
  refine redAbs l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) hAll hD ?_ ξ hξ hTI (φ a) (Ideal.mem_map_of_mem _ ha)
  intro ζ hV hT _ hGd
  obtain ⟨h1, h2⟩ := hNice ζ hV hT _ rfl hGd (hFree _ hGd)
  exact fixLe l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S ζ hV.1 hT (hFix ζ _ hV.1 h1 h2)
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaU
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.W
def HidaUAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 1 ≤ n → ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.HidaPropsAlt ι J Λ ∧ Pa.HasAut B J
end UpperTheory.V.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HostNumberS
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut
namespace UpperTheory.V.UnitaryThreeInertia
def HostRigid_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r →
    (_root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) → F.Rigid r
def HostNumber_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K → ∃ C : ℕ,
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∃ φ : Gam Ω S,
    (∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r → TypeI F.η r → (_root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) →
      (r φ).mat.trace ≠ (F.rz (PadicAlgCl l) φ).mat.trace) ∧
    ∀ (n : ℕ) (r : Fin n → (Gam Ω S →* GG 3 (PadicAlgCl l))),
      (∀ i, F.IsCharZeroPt g₁ (r i) ∧ TypeI F.η (r i) ∧ _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r i (toGS Ω _ s)).mat) →
      (∀ i i', MatIso F.η.ker (mats (r i)) (mats (r i')) → i = i') →
      (∑ i, vl1 l ((r i φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace)) * Real.log l ≤ ((l : ℝ) * N * e) ^ C
end UpperTheory.V.UnitaryThreeInertia
end
end
end

