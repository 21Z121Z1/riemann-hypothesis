import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexification
section
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.DefRead.Transport

section General

variable {Ks LL WL C : Type} [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Algebra Ks ℂ] [Algebra LL ℂ] [IsScalarTower Ks LL ℂ]

def phiBil (e : C →ₗ[Ks] WL) : ℂ →+ C →+ ℂ ⊗[LL] WL :=
  AddMonoidHom.mk' (fun z => ((TensorProduct.mk LL ℂ WL z).toAddMonoidHom.comp e.toAddMonoidHom))
    (fun a b => by ext f; exact TensorProduct.add_tmul a b (e f))

theorem phiBil_compat (e : C →ₗ[Ks] WL) (r : Ks) (z : ℂ) (f : C) :
    phiBil (LL := LL) e (r • z) f = phiBil (LL := LL) e z (r • f) := by
  show (r • z) ⊗ₜ[LL] e f = z ⊗ₜ[LL] e (r • f)
  rw [map_smul, ← algebraMap_smul LL r (e f), TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    algebraMap_smul LL r z]

def phi (e : C →ₗ[Ks] WL) : ℂ ⊗[Ks] C →ₗ[ℂ] ℂ ⊗[LL] WL where
  toFun := TensorProduct.liftAddHom (phiBil (LL := LL) e) (phiBil_compat e)
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z f =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show (c • z) ⊗ₜ[LL] e f = c • (z ⊗ₜ[LL] e f)
      rw [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

@[simp] theorem phi_tmul (e : C →ₗ[Ks] WL) (z : ℂ) (f : C) : phi e (z ⊗ₜ[Ks] f) = z ⊗ₜ[LL] e f :=
  TensorProduct.liftAddHom_tmul (phiBil (LL := LL) e) (phiBil_compat e) z f

theorem phi_comm (e : C →ₗ[Ks] WL) (a : C →ₗ[Ks] C) (r : WL →ₗ[LL] WL) (h : ∀ f, e (a f) = r (e f)) :
    phi e ∘ₗ a.baseChange ℂ = r.baseChange ℂ ∘ₗ phi e := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [h]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

theorem phi_bijective (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) :
    Function.Bijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap)) := by
  let bW : Module.Basis (Fin n) Ks (Submodule.span Ks (Set.range b)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) Ks WK := bW.map (LinearEquiv.ofEq _ _ hspK)
  let bC : Module.Basis (Fin n) Ks C := bK.map e.symm
  let bL : Module.Basis (Fin n) LL WL := Module.Basis.mk hliL (by rw [hspL])
  let cC := Algebra.TensorProduct.basis ℂ bC
  let cL := Algebra.TensorProduct.basis ℂ bL
  have key : phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) = (cC.equiv cL (Equiv.refl _)).toLinearMap := by
    refine cC.ext fun j => ?_
    show _ = (cC.equiv cL (Equiv.refl _)) (cC j)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [cC, cL, bC, bK, bW, bL, Module.Basis.span_apply]
  rw [key]
  exact (cC.equiv cL (Equiv.refl _)).bijective

theorem transport_general {H G X : Type} [Group G] [Group H] [DecidableEq X] [MulAction H X]
    (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) (ρ0 : G → (WL →ₗ[LL] WL))
    (act : G → C →ₗ[Ks] C) (he : ∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) (s : G → ℂ) (φ : H →* G)
    (A : X → Submodule ℂ (ℂ ⊗[Ks] C)) (hA : DirectSum.IsInternal A)
    (hinv : ∀ (h : H) (y : X), ∀ v ∈ A y, (act (φ h)).baseChange ℂ v ∈ A (h • y)) :
    ∃ A' : X → Submodule ℂ (ℂ ⊗[LL] WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, (s (φ h) • (ρ0 (φ h)).baseChange ℂ) v ∈ A' (h • y) := by
  let Ψ := LinearEquiv.ofBijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap))
    (phi_bijective WK n b hliK hspK hliL hspL e)
  let o := Submodule.orderIsoMapComap Ψ
  refine ⟨fun y => o (A y), ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
    refine ⟨iSupIndep.map_orderIso o hA.1, ?_⟩
    rw [← o.map_iSup, hA.2, o.map_top]
  · intro h y v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map).1 hv
    have hc := LinearMap.congr_fun (phi_comm (WK.subtype ∘ₗ e.toLinearMap) (act (φ h)) (ρ0 (φ h))
      (fun f => he _ f)) u
    refine Submodule.mem_map.2 ⟨s (φ h) • (act (φ h)).baseChange ℂ u, (A (h • y)).smul_mem _ (hinv h y u hu), ?_⟩
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.smul_apply, map_smul]
    show s (φ h) • phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) _ = s (φ h) • (ρ0 (φ h)).baseChange ℂ (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) u)
    rw [hc]

end General

open GlobalTheory.DefRead in

theorem transport : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  intro Ks LL WL C H G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ WK n b _ hliK hspK hliL hspL e ρ0 χ act he φ A hA hinv
  letI : Algebra Ks ℂ := (σ.comp (algebraMap Ks LL)).toAlgebra
  letI : Algebra LL ℂ := σ.toAlgebra
  haveI : IsScalarTower Ks LL ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨A', h1, h2⟩ := transport_general (X := X) WK n b hliK hspK hliL hspL e (fun g => ρ0 g) act he
    (fun g => σ (((χ g)⁻¹ : LLˣ) : LL)) φ A hA hinv
  exact ⟨A', h1, fun h y v hv => by rw [twBC_apply]; exact h2 h y v hv⟩

end GlobalTheory.DefRead.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandardStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_kernel_class_scalar_integral_standard : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → ∃ c1 : D.what₂.LL, D.what₂.embLL c1 * (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹) = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) ∧ ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c1) := by
  first | exact @GlobalTheory.TwistClassScalar.twist_class_scalar | exact GlobalTheory.TwistClassScalar.twist_class_scalar | (intros; apply GlobalTheory.TwistClassScalar.twist_class_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackNonvanishingOfPulledSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistNZ

theorem mem_nz_iff {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι)
    {x : Y} (hk : x ∈ H.U k) : x ∈ nonzeroLocus s ↔ x ∈ Y.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg Y.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, Y.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, Y.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem twistPull_nonzero : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := by
  intro S A _ L hL T ψ m hm a b α s s' H p hp
  have hcov : ∀ y : A.left, ∃ i, y ∈ L.U i := fun y => by
    have : y ∈ (⨆ i, L.U i : A.left.Opens) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  obtain ⟨i0, h0⟩ := hcov ((snd T A).left.base p)
  obtain ⟨i1, h1⟩ := hcov (m.left.base p)
  let j : Fin 2 → L.ι := ![i0, i1]
  have e₀ : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hpj : p ∈ LB.wchart L ![(snd T A).left, m.left] j := by
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · exact h0
    · exact h1

  have hψ : ψ.left.base p ∈ (LPow A L b T).U (fun _ => j 1) := by
    refine Set.mem_iInter.2 fun _ => ?_
    show ((snd T A).left.base (ψ.left.base p)) ∈ (L.U i1 : Set A.left)
    have : (ψ.left ≫ (snd T A).left).base p = m.left.base p := by rw [e₀]
    rw [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [this]; exact h1
  have h2 : ψ.left.base p ∈ (T ⊗ A).left.basicOpen (s.f (fun _ => j 1)) :=
    (mem_nz_iff s _ hψ).1 hp
  have h3 : p ∈ (T ⊗ A).left.basicOpen ((ψ.left.app _).hom (s.f (fun _ => j 1))) := by
    rw [← Scheme.preimage_basicOpen]; exact h2
  have e := congrArg (T ⊗ A).left.basicOpen (H j)
  dsimp only at e
  erw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (α.s j).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hp4 := e.ge ⟨hpj, hpj, h3⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hp4.2⟩

end GlobalTheory.TwistNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
section
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Good

open scoped nonZeroDivisors

theorem exists_vAdd_ge {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℕ) :
    ∃ a : K, a ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vAdd w a) ∧ ∀ w ∈ S, (B : ℤ) ≤ vAdd w a := by
  classical
  let I : Ideal (𝓞 K) := ∏ w ∈ S, w.asIdeal ^ B
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha0 : algebraMap (𝓞 K) K r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
  have hmem : algebraMap (𝓞 K) K r ∈
      (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) := by
    have e : (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) = ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      simp only [Equiv.refl_apply, neg_neg, zpow_natCast, I]
      rw [← FractionalIdeal.coeIdealHom_apply, map_prod]
      simp [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [e]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hrI, rfl⟩
  refine ⟨_, ha0, fun w => ?_, fun w hw => ?_⟩
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg] at h
    split_ifs at h
    · exact le_trans (by positivity) h
    · exact h
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg, if_pos hw] at h
    exact h

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem exists_twist_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) :
    ∃ a : c.F, a ≠ 0 ∧ (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) ∧ ∀ w, s.hi w ≤ (vAdd w a : ℝ) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 c.F)) := s.finite_lo.toFinset ∪ s.finite_hi.toFinset
  let B : ℕ := ⌈∑ w ∈ S, (|s.lo w| + |s.hi w|)⌉₊
  have hB : ∀ w ∈ S, |s.lo w| + |s.hi w| ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => |s.lo w| + |s.hi w|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hw).trans (Nat.le_ceil _)
  obtain ⟨a, ha0, hpos, hS⟩ := exists_vAdd_ge S B
  refine ⟨a, ha0, fun w => ?_, fun w => ?_⟩
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := neg_abs_le (s.lo w)
      push_cast at h2
      linarith [abs_nonneg (s.hi w)]
    · have : s.lo w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_left _ (s.finite_lo.mem_toFinset.2 h))
      rw [this, add_zero]; exact_mod_cast hpos w
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := le_abs_self (s.hi w)
      push_cast at h2
      linarith [abs_nonneg (s.lo w)]
    · have : s.hi w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_right _ (s.finite_hi.mem_toFinset.2 h))
      rw [this]; exact_mod_cast hpos w

theorem cnorm_smul {ι : Type} [Fintype ι] (k : ℂ) (u : ι → ℂ) : Formalism.HermitianLatticesTheory.cnorm (k • u) = ‖k‖ * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have : ∑ i, ‖(k • u) i‖ ^ 2 = ‖k‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

section Abstract

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem lattice_transfer (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set V) = ⊤) :
    L'.FG ∧ Submodule.span K (L' : Set W) = ⊤ ∧ Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  let ψ : V →ₗ[𝓞 K] W :=
    { toFun := fun f => a⁻¹ • φ f
      map_add' := fun f f' => by rw [map_add, smul_add]
      map_smul' := fun m f => by
        rw [RingHom.id_apply, ← algebraMap_smul K m f, map_smul, ← algebraMap_smul K m (a⁻¹ • φ f),
          smul_smul, smul_smul, mul_comm] }
  have hle : L' ≤ L.map ψ := fun g hg => by
    refine ⟨a • φ.symm g, hout g hg, ?_⟩
    show a⁻¹ • φ (a • φ.symm g) = g
    rw [map_smul, φ.apply_symm_apply, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hFG' : L'.FG := by
    have := isNoetherian_of_fg_of_noetherian _ (hFG.map ψ)
    exact isNoetherian_submodule.mp this _ hle
  have hspan' : Submodule.span K (L' : Set W) = ⊤ := by
    have hsub : Submodule.span K (L : Set V) ≤ (Submodule.span K (L' : Set W)).comap (φ : V →ₗ[K] W) := by
      refine Submodule.span_le.2 fun f hf => Submodule.mem_comap.2 ?_
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    rw [eq_top_iff]
    intro g _
    have h := hsub (show φ.symm g ∈ Submodule.span K (L : Set V) by rw [hspan]; trivial)
    simpa using h
  refine ⟨hFG', hspan', ?_⟩
  unfold Formalism.HN.rkK
  rw [hspan, hspan', finrank_top, finrank_top]
  exact φ.symm.finrank_eq

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in

theorem hasGram_transfer (φ : V ≃ₗ[K] W) (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (h : ∀ σ f, N' σ (φ f) = t σ * N σ f) (hN : HasGram N) : HasGram N' := by
  obtain ⟨⟨n, ⟨b, X⟩, hX⟩⟩ := hN
  refine ⟨⟨n, ⟨(b.map φ, fun v => ((t v.embedding : ℂ)⁻¹) • X v), fun v => ?_⟩⟩⟩
  have hk : ((t v.embedding : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (ht _).ne')
  have hdet := (hX v).1
  refine ⟨?_, fun y => ?_⟩
  · show IsUnit ((((t v.embedding : ℂ)⁻¹) • X v).det)
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit hk)).mul hdet
  · show Formalism.HermitianLatticesTheory.normAt (b.map φ) (fun v => ((t v.embedding : ℂ)⁻¹) • X v) v y = N' v.embedding y
    have := invertibleOfNonzero hk
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.inv_smul _ _ hdet, invOf_eq_inv]
    have hvec : Formalism.HermitianLatticesTheory.vecAt (b.map φ) v y = Formalism.HermitianLatticesTheory.vecAt b v (φ.symm y) := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr]
    rw [hvec, Matrix.smul_mulVec, cnorm_smul, ← Formalism.HermitianLatticesTheory.fcoord, ← Formalism.HermitianLatticesTheory.normAt, (hX v).2,
      ← φ.apply_symm_apply y, h, φ.apply_symm_apply]
    rw [inv_inv, Complex.norm_real, Real.norm_of_nonneg (ht _).le]

end Abstract

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem twist_goodOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G _hU hG hgood
  obtain ⟨hGram, hFG, hspan⟩ := hgood
  obtain ⟨φ, hφ, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := exists_twist_scalar s
  obtain ⟨hFG', hspan', hrk⟩ := lattice_transfer φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _)) hFG hspan
  refine ⟨⟨hasGram_transfer φ _ _ s.cInf s.cInf_pos (fun σ f => ?_) hGram, hFG', hspan'⟩, hrk⟩
  show petOn U x V dict Z (G + G₀) σ (φ f : Rul Xo c) = s.cInf σ * petOn U x V dict Z G σ (f : Rul Xo c)
  rw [hφ, petOn, petOn, GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul E H Dw l Xo c r U x Z G₀ s G hG _ f.2.2]

end GlobalTheory.FlatTw.Good
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEq
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.RankHostFacts

theorem two_le_r_and_fdeg (D : D7) : 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  refine ⟨Formalism.L2.Geo.two_le_r D, ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
  rw [Formalism.L2.Pj.hostSize_finrank D]
  omega

theorem main : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f :=
  two_le_r_and_fdeg

end GlobalTheory.RankHostFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def UnitChartAt (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X) :
    Prop :=
  ∃ (R : Type) (_ : CommRing R) (ξ : Sp R ⟶ X) (c : (Localization.Away (p : R))ˣ), IsOpenImmersion ξ ∧
    x ∈ Set.range ξ ∧ ∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) →
      ∀ ψ : Localization.Away (p : R) →+* ℂ_[p], ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
        ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (c : Localization.Away (p : R)) - κ‖ < ‖κ‖

def DensSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → Flat s → LocallyOfFiniteType s →
      Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty →
      ∀ (R : Type) [CommRing R] (ξ : Sp R ⟶ X), IsOpenImmersion ξ →
        (∃ x ∈ Set.range ξ, x ∉ X.basicOpen (p : Γ(X, ⊤))) → ∃ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ)

def RestrictSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s →
      Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw → ∀ (n : ℕ) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]),
      (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x ∈ closure (Xw : Set X), ChartAt p n Xw K x) →
      ∃ (X₁ : Scheme.{0}) (s₁ : X₁ ⟶ Sp V) (Xw₁ : X₁.Opens) (K₁ : (Sp 𝓞_ℂ_[p] ⟶ X₁) → Set ℂ_[p]),
        IsIntegral X₁ ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁ ∧ IsProjOver s₁ ∧ Flat s₁ ∧
        Xw₁ ≤ X₁.basicOpen (p : Γ(X₁, ⊤)) ∧ GeomIrr s₁ Xw₁ ∧ (∀ yb, IsTest p Xw₁ yb → (K₁ yb).Nonempty) ∧
        (∀ x : X₁, ChartAt p n Xw₁ K₁ x) ∧
        ∀ yb, IsTest p Xw yb → ∃ yb₁, IsTest p Xw₁ yb₁ ∧ K yb ⊆ K₁ yb₁

def ModSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
      IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw →
      ∀ (n : ℕ) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]),
      (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, ChartAt p n Xw K x) →
      ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp V) (Xw' : X'.Opens) (K' : (Sp 𝓞_ℂ_[p] ⟶ X') → Set ℂ_[p]),
        IsIntegral X' ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ IsProjOver s' ∧ Flat s' ∧
        Xw' ≤ X'.basicOpen (p : Γ(X', ⊤)) ∧ GeomIrr s' Xw' ∧ (∀ yb, IsTest p Xw' yb → (K' yb).Nonempty) ∧
        (∀ x : X', UnitChartAt p Xw' K' x) ∧
        ∀ yb, IsTest p Xw yb → ∃ yb', IsTest p Xw' yb' ∧ K yb ⊆ K' yb'

def PrincSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
      IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw →
      ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]),
      (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, UnitChartAt p Xw K x) →
      ∃ ρ : ℝ, ∀ yb, IsTest p Xw yb → ∀ κ ∈ K yb, ‖κ‖ = ρ

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedClassOfCmHost
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem host_unr : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE;
    GlobalTheory.UCls.Unr D.host.E := fun D =>
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  Formalism.L2.Pj.unramBridge_holds D.host.E (Formalism.L2.Pj.cmUnram_conj D)

end GlobalTheory.MassLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  first | exact @GlobalTheory.InertVacLag.vac_not_mem_augAt | exact GlobalTheory.InertVacLag.vac_not_mem_augAt | (intros; apply GlobalTheory.InertVacLag.vac_not_mem_augAt <;> assumption)
end

