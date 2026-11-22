import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CcExCore

open GlobalTheory.ClsVal.Cmp

theorem exists_ccIs_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hC i A.μ0 hO.lift.std
  have hM := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs0
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) O.s0 := by
    rw [hs0, chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) O.s0 = W),
      MuVal W (T.chiW ((i : ℕ) + 1) O.s0) (castDict hV (T.mu ((i : ℕ) + 1) O.s0)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) O.s0) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) O.s0) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ
    exact ⟨hT.laws.muVal _ (inR i) _ hσ, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ O.hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (O.dict 1).1
  exact GlobalTheory.AdTh.CcEx.exists_ccIs_of_pair hci hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt _ hσ (hT.laws.unf _ (inR i) _ hσ) hr1
    hT.laws.pins.2.1.2 hdom hV0 h1 h2 h3 h4 h5 _ _ (fun k => (hM k).1) (fun k => (hM k).2.1) (fun k => (hM k).2.2.1)
    (hC.thP.vP i A.μ0).1 _

end GlobalTheory.AdTh.CcExCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLift
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds

namespace GlobalTheory.LowForm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem op_idem {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
    simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem adjoint_eq_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (E : H →ₗ[ℂ] H)
    (h1 : ∀ u, E (E u) = E u) (h2 : ∀ x, E x = x → ∀ y, ⟪x, E y⟫_ℂ = ⟪x, y⟫_ℂ) : LinearMap.adjoint E = E := by
  refine LinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [LinearMap.adjoint_inner_left, ← h2 _ (h1 x) y, ← inner_conj_symm, ← h2 _ (h1 y) x, inner_conj_symm]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem eC_idem_at (hr : R.grp_record) (σ : D.what₂.LL →+* ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) σ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftScalarCompare.eC_idem hr
  unfold RealDat.eC at h1 h2 ⊢
  refine ⟨fun g k => congrArg σ ((sg0 D A).injective (h1 g k)), fun g => ?_⟩
  have := h2 g
  simp only [← map_mul, ← map_sum] at this ⊢
  exact congrArg σ ((sg0 D A).injective this)

theorem projH_idem (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    projH R i σ (projH R i σ x) = projH R i σ x := op_idem (R.gW i σ) (eC_idem_at h.grp.record σ) x

theorem projH_adjoint (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (projH R i σ) = projH R i σ :=
  adjoint_eq_self _ (projH_idem h i σ) fun _ hx y => GlobalTheory.LiftScalarCompare.adjoint_idem (R.gW i σ)
    (GlobalTheory.gW_norm_eq R h.models.HW h.models.gW h.models.νW i σ) (eC_idem_at h.grp.record σ) hx y

open Classical in
variable (R) in

def blkChar (i : Fin D.R.m) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR A.μ0 PP

def conjChar (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (m PP)

theorem twVal_zero {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    twVal χ 0 P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  unfold twVal
  simp

theorem isConjChars_at (h : R.Char F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s)
    {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    IsConjChars R i A.μ0 s μ' η' (conjChar s (blkChar R i)) := by
  obtain ⟨μH, a1, a2⟩ := GlobalTheory.ConjMuChar.exists_galConj_chrEq R F h i σ s hσ μ' hμ
  obtain ⟨ηH, b1, b2⟩ := GlobalTheory.EtaConjChar.exists_galConj_eta R F h σ s hσ η' hη
  obtain ⟨μB, -, c1, -, -, -, c2⟩ := isConjChars_base R h i A.μ0
  refine ⟨μH, ηH, a1, b1, a2, b2, fun PP hP a k u hk hu => Units.ext ?_⟩
  have e1 := a1 PP k
  have e2 := c1 PP k
  rw [twVal_zero, twVal_zero] at e1 e2
  have e3 := c2 PP hP a k u hk hu
  rw [e1]
  exact congrArg s ((congrArg Units.val e3).trans e2)

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (r : ℕ) (hr : r ≤ n) (t s' : ℕ) (Pg Q : Finset (Pl D.host.E))
    (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => conjChar s m, conjChar s m⟩ x : ℂˣ) : ℂ) =
      s ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => m, m⟩ x : ℂˣ) : ℂ) := by
  unfold levFn
  have e : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  simp only [e, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rfl

theorem chrOf_conj (i : Fin D.R.m) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : levJ R i A.μ0) :
    ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv (conjChar s m)) k : ℂˣ) : ℂ) =
      s ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) k : ℂˣ) : ℂ) :=
  levFn_conj (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q A.μ0) s m (Formalism.UG.bc (Lev.swapAE D) k.1.1)

theorem chr_at (h : R.Char F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s)
    (χ' : levJ R i A.μ0 →* ℂˣ)
    (hχ : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjVal σ (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ)) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv (conjChar s (blkChar R i))) = χ' := by
  refine MonoidHom.ext fun k : levJ R i A.μ0 => Units.ext ?_
  refine (hχ k).elim fun y hy => ?_
  have h1 := hy.1
  have h2 := hy.2
  have e1 := congrArg Units.val (DFunLike.congr_fun (chr_base R h i A.μ0) k)
  have e2 := chrOf_conj (R := R) i s (blkChar R i) k
  have e3 : ((χ' k : ℂˣ) : ℂ) = s (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) :=
    h2.symm.trans ((hσ.1 y).trans (congrArg s h1))
  exact e2.trans ((congrArg s e1).trans e3.symm)

theorem isLevelVec_at (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    (hf : Datum.IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q A.μ0)
      m f₀ f := by
  rw [Q_base h.lev]
  unfold Datum.IsThPVecOf at hf
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
    intro y
    unfold Datum.omegaQ
    simp
  simp only [omegaG_triv, hQ]
  exact hf

theorem hookPlus_le (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i id) : hookPlus D i ≤ mainTerm D i σ := by
  have e : mainTerm D i σ = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) := by
    unfold mainTerm GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
    simp only [Nat.cast_mul]
    rfl
  rw [e, h]
  unfold hookPlus GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (Nat.cast_pos.2 (hookProd_pos _)) (Nat.cast_le.2 ?_)
  exact Nat.le_mul_of_pos_right _ (hookProd_pos _)

theorem eq_of_low_at (hW : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec} (hv : IsExtVec (R.MW i σ) v)
    {x y : (R.HW i σ).H}
    (h : ∀ w : ∀ ρ, lowT (R.MW i σ) ρ, (R.HW i σ).e x (fun ρ => w ρ) = (R.HW i σ).e y fun ρ => w ρ) : x = y := by
  have h0 : (R.HW i σ).e (x - y) v = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 (h fun ρ => ⟨v ρ, (hv ρ).2.1⟩)
  have h1 := (hW i σ).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v (fun τ => (hv τ).1) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem lower_of_parts {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (P : ι → Submodule ℂ Y) (S : ι → Prop) (a : ℝ) (h1 : LinearMap.adjoint e = e) (h2 : ∀ y, e (e y) = e y)
    (h3 : (⨆ (k) (_ : S k), P k) = ⊤)
    (h4 : ∀ k, P k ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) ∧ a ≤ Real.log l)
    (h5 : ∀ x, th x = e (T x)) : ∀ x ∈ (LinearMap.ker th)ᗮ, Real.exp a * ‖x‖ ^ 2 ≤ ‖th x‖ ^ 2 := by
  obtain rfl : th = e ∘ₗ T := LinearMap.ext h5
  refine GlobalTheory.mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts X Y ι T e P _ (Real.exp_pos a) h1 h2 ?_ fun k => ?_
  · exact top_le_iff.1 (h3.ge.trans (iSup₂_le fun k _ => le_iSup P k))
  · by_cases hk : P k = ⊥
    · refine ⟨_, le_rfl, fun y hy => ?_⟩
      rw [hk, Submodule.mem_bot] at hy
      simp [hy]
    · obtain ⟨l, a1, a2, a3⟩ := h4 k hk
      exact ⟨l, (Real.le_log_iff_exp_le a1).1 a3, a2⟩

open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature in

theorem exists_full_lift (hA : AdelicLiftScalar R F) (h : R.Char F) (i : Fin D.R.m) {b : ℝ} (hb : Sizes D i b)
    (ht : PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s) {v : (R.MW i σ).Vec}
    (hv : IsExtVec (R.MW i σ) v) {c₀ μ' η' c c₁ H j th} (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) :
    ∃ T : H.H →ₗ[ℂ] (R.HW i σ).H, (∀ x, th x = projH R i σ (T x)) ∧
      ∀ ev, typePart R i σ A.μ0 R.triv ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ A.μ0 R.triv ev, T (adjLev R.triv T x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hμ := hd.1
  have hη := hd.2.1
  have hF := hd.2.2.1
  refine hd.2.2.2.elim fun ω a => a.elim fun f₀ a => a.elim fun f a => a.elim fun B a => a.elim fun io a =>
    a.elim fun thP a => ?_
  refine hF.model.elim fun χ' hχ => ?_
  have hH := hχ.2
  rw [← chr_at h i hσ χ' hχ.1] at hH
  have key := hA h i b hb A.μ0 ht σ s hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_at h i hσ hμ hη) ω a.1 B a.2.2.1 f₀ f
    (isLevelVec_at h i σ _ a.2.1) a.2.2.2.1 c hF.coef io a.2.2.2.2.1 (R.νV i A.μ0) (R.fdV i A.μ0) (h.models.νV i A.μ0) _
    (R.B.L i A.μ0).pres.y (R.B.L i A.μ0).pres.reps H hH
  refine key.1.elim fun T hT => ⟨T, fun x => eq_of_low_at h.models.HW hv fun w => ?_, key.2 T hT⟩
  have e1 : (R.HW i σ).e (T x) (fun ρ => w ρ) = thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ w) :=
    funext fun g => (hT x w g).2.trans
      (GlobalTheory.BaseScalar.integrableOn_of_isThetaLift a.2.2.2.2.2.1 x (PiTensorProduct.tprod ℂ w) g).2.symm
  have e2 : (R.HW i σ).e (projH R i σ (T x)) (fun ρ => w ρ) = R.eWf i σ ((R.HW i σ).e (T x) fun ρ => w ρ) :=
    congrArg (fun U : MMap (R.MW i σ) => U fun ρ => w ρ) (e_projH h.models.gW i σ (T x))
  exact (a.2.2.2.2.2.2 x w).trans (e2.trans (congrArg (R.eWf i σ) e1)).symm

theorem parts_scalar (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) {b : ℝ}
    (hlog : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i id)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] (T : X →ₗ[ℂ] (R.HW i σ).H)
    (hT : ∀ ev, typePart R i σ A.μ0 R.triv ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ A.μ0 R.triv ev, T (adjLev R.triv T x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l) :
    ∀ ev, partH R i σ ev ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ y ∈ partH R i σ ev, T (LinearMap.adjoint T y) = (l : ℂ) • y) ∧
      GlobalTheory.BigOn.lowB D i b ≤ Real.log l := by
  intro ev hev
  have e := LiftLower.typePart_base h.lev i σ ev
  refine (hT ev (fun h0 => hev (e.symm.trans h0))).elim fun l a => ?_
  refine ⟨l, a.1, fun y hy => ?_, le_trans (sub_le_sub_right (hookPlus_le i σ hlog) _) a.2.2⟩
  have e1 := LinearMap.congr_fun (GlobalTheory.BaseScalar.adjLev_triv R T) y
  have e2 := a.2.1 y (e.ge hy)
  exact (congrArg T e1).symm.trans e2

open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature in

theorem conjLift_lower (hA : AdelicLiftScalar R F) (h : R.Char F) (i : Fin D.R.m) {b : ℝ} (hb : Sizes D i b)
    (ht : PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s) {v : (R.MW i σ).Vec}
    (hv : IsExtVec (R.MW i σ) v) (hlog : logHookSum i (lab σ) = logHookSum i id) {c₀ μ' η' c c₁ H j th}
    (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) :
    ∀ x ∈ (LinearMap.ker th)ᗮ, Real.exp (GlobalTheory.BigOn.lowB D i b) * ‖x‖ ^ 2 ≤ ‖th x‖ ^ 2 := by
  refine (exists_full_lift hA h i hb ht hσ hv hd).elim fun T hT => ?_
  have p1 := projH_adjoint h i σ
  have p2 := projH_idem h i σ
  have p3 := GlobalTheory.PrincipalDecomp.iSup_partH_eq_top R F h i σ (schurMult_of_models R h.models.HW i σ)
  have p4 := parts_scalar h i σ (b := b) hlog T hT.2
  exact lower_of_parts T th (projH R i σ) (partH R i σ) (IsNormSys R i) _ p1 p2 p3 p4 hT.1

end GlobalTheory.LowForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspace
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.LiftMod

theorem kstable_of_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (U : Submodule ℂ V) (h : ∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ U, units act a b u ∈ U) : KStable act U := by
  intro X hX u hu
  have hXs : X = ∑ a, ∑ b, X a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hXs, map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun a _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun b _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  by_cases hab : sameBlock a b
  · refine U.smul_mem _ (h a b ?_ u hu)
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (hab : False).elim
    · exact (hab : False).elim
    · rfl
  · rw [hX a b hab, zero_smul]; exact U.zero_mem

theorem lift_mod : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ (μ : Ix p q → ℚ), ∀ v ∈ N', (∀ c, act (Eab c c) v - ((μ c : ℚ) : ℂ) • v ∈ N) → (∀ c d, posC c d → act (Eab c d) v ∈ N) → ∃ v' ∈ N', v' ∈ hwSub act μ ∧ v - v' ∈ N := by
  intro p q V _ _ act hG N N' hN hN' μ v hv h1 h2
  obtain ⟨hLie, hwt, hloc⟩ := hG
  obtain ⟨U, hvU, hUfd, hUst, -⟩ := hloc {v}
  have hU : KStable act U := kstable_of_units act U hUst
  have hvU' : v ∈ U := hvU v (Finset.mem_singleton_self v)
  haveI : FiniteDimensional ℂ U := hUfd
  let W : Submodule ℂ V := N' ⊓ U
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (inf_le_right : W ≤ U)
  have sW : KStable act W := fun X hX w hw => ⟨hN' X hX w hw.1, hU X hX w hw.2⟩
  have hKL : Formalism.MainNotions.SchurIrreducible.IsKLieAct act := fun Y Z _ _ => hLie Y Z
  obtain ⟨T', hT'W, hTN, hhw⟩ := GlobalTheory.DegKeep.joint_lift (ι := Unit) (fun _ => act) (fun _ => hKL) (fun _ v => hwt v)
    (fun w w' hne => absurd (Subsingleton.elim w w') hne) W N (fun _ => sW) (fun _ => hN) (fun _ => μ) v ⟨hv, hvU'⟩
    (fun _ c => h1 c) (fun _ c d hcd => h2 c d hcd)
  exact ⟨T', hT'W.1, hhw (), hTN⟩

end GlobalTheory.HoweR.LiftMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimensionalFinitePartsWeilTrans
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilContF

theorem adeleJoin_zero_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    GlobalTheory.WeilCont.adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  simp [GlobalTheory.WeilCont.adeleJoin]
  rfl

theorem sum_mul_zero_prod {κ : Type} [Fintype κ] {A B : Type} [CommRing A] [CommRing B] (z : κ → A × B)
    (y : κ → B) : (∑ i, z i * ((0 : A), y i)) = ((0 : A), ∑ i, (z i).2 * y i) := by
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem dotProduct_adeleJoin_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (z : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = pairA F 0 ((fun i => (z i).2) ⬝ᵥ y) := by
  simp only [dotProduct, GlobalTheory.WeilCont.adeleJoin, pairA, Pi.zero_apply, map_zero]
  exact sum_mul_zero_prod (A := InfiniteAdeleRing F) (B := FiniteAdeleRing (𝓞 F) F) z y

end GlobalTheory.WeilContF

namespace GlobalTheory.WeilContF

theorem exists_local_finite_parts_F : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        om p Φ = ∑ i, pureA F (f i) (g i) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om hom Φ hΦ p0
  obtain ⟨pres, impl⟩ := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ co
    hco om hom
  obtain ⟨L₁, L₂, hL₁, hL₂, hinv⟩ := GlobalTheory.T.exists_openSubgroups_schroedinger_fix_continuousChar F B.ψ hB.std.1 κ Φ hΦ
  obtain ⟨N, hN, L₁', L₂', hL₁', hL₁c, hL₂', hNL⟩ := GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage F E σ nT nS JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0
  have hK := GlobalTheory.T.isCompact_annihilator_openSubgroup_finiteAdeles F B.ψ hB.std κ L₂' hL₂'
  obtain ⟨m, g, y, hg, hgy, hrep⟩ := GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition F κ L₁' hL₁' hL₁c _ hK
  refine ⟨N, hN, m, g, y, hg, hgy, fun p hp => ?_⟩
  have fix : ∀ x ∈ L₁', ∀ y₁ ∈ L₂', schr B.ψ (GlobalTheory.WeilCont.adeleJoin F 0 x,
      GlobalTheory.WeilCont.adeleJoin F 0 y₁) (om p Φ) = om p Φ := by
    intro x hx y₁ hy₁
    obtain ⟨x', hx', y', hy', he⟩ := hNL p hp x hx y₁ hy₁
    have := impl p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y')) Φ hΦ
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, hinv x' hx' y' hy', he] at this
    exact this.symm
  refine hrep (om p Φ) (pres p Φ hΦ) ?_ ?_
  · intro x hx z
    have := congrFun (fix x hx 0 (zero_mem _)) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul] at this
    exact this
  · intro z hz y₁ hy₁
    have := congrFun (fix 0 (zero_mem _) y₁ hy₁) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, zero_dotProduct, mul_zero, add_zero,
      GlobalTheory.WeilContF.dotProduct_adeleJoin_zero] at this
    exact (mul_eq_right₀ hz).mp this

end GlobalTheory.WeilContF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitaryStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_GL_embedding_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ t : E →ₐ[F] Fv F v,
    ∃ K : GL (Fin a') (Fv F v) →* UA σ G.V'.J, ∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t := by
  first | exact @GlobalTheory.LeviAtPlace.levi_at_place | exact GlobalTheory.LeviAtPlace.levi_at_place | (intros; apply GlobalTheory.LeviAtPlace.levi_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilHomFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localWeilHom_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] (σL : L →+* L) (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L)
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) → (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) →
    ∃ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) := by
  first | exact @GlobalTheory.LocalWeilHom.local_weil_hom | exact GlobalTheory.LocalWeilHom.local_weil_hom | (intros; apply GlobalTheory.LocalWeilHom.local_weil_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localWeilOperators_supportedAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  first | exact @GlobalTheory.LocalWeilOps.local_ops | exact GlobalTheory.LocalWeilOps.local_ops | (intros; apply GlobalTheory.LocalWeilOps.local_ops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataGivenLevelCoeffMapsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_given_level_coeffMaps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → Finite T0 → QGuard R → ∀ i : Fin D.R.m, VStd D i → ∀ (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  first | exact @GlobalTheory.PinnedDataGiven.exists_pins_given | exact GlobalTheory.PinnedDataGiven.exists_pins_given | (intros; apply GlobalTheory.PinnedDataGiven.exists_pins_given <;> assumption)
end

