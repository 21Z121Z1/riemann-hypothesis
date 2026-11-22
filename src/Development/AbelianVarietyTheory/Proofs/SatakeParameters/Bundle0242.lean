import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.Bundle0004
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDense
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0155
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0153
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrobStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  first | exact @GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | exact GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | (intros; apply GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatePlaceCompletionIsoTameStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_place_completion_iso_tame : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v) → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  first | exact @GlobalTheory.TypeBlockConj.main | exact GlobalTheory.TypeBlockConj.main | (intros; apply GlobalTheory.TypeBlockConj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensional
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ConjSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def gen (t : (E →+* ℂ) × Fin n × Fin n) : infU E n → ℂ := fun x => (cEmb t.1 x.1).val t.2.1 t.2.2

def mono (l : List ((E →+* ℂ) × Fin n × Fin n)) : infU E n → ℂ := (l.map gen).prod

variable (E n) in

def polys (N : ℕ) : Submodule ℂ (infU E n → ℂ) :=
  Submodule.span ℂ (mono '' {l | l.length ≤ N})

theorem polys_fd (N : ℕ) : FiniteDimensional ℂ (polys E n N) :=
  FiniteDimensional.span_of_finite ℂ ((List.finite_length_le _ N).image _)

theorem polys_mono {N N' : ℕ} (h : N ≤ N') : polys E n N ≤ polys E n N' :=
  Submodule.span_mono (Set.image_mono fun _ hl => le_trans hl h)

variable (E n) in

abbrev gens : Set (infU E n → ℂ) := {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}

theorem exists_mono_of_mem_closure {f : infU E n → ℂ} (hf : f ∈ Submonoid.closure (gens E n)) :
    ∃ l, f = mono l := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    exact ⟨[(τ, i, j)], by funext x; simp [mono, gen]⟩
  | one => exact ⟨[], by simp [mono]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨l, rfl⟩ := hf
    obtain ⟨l', rfl⟩ := hg
    exact ⟨l ++ l', by simp [mono]⟩

theorem exists_polys_of_mem_adjoin {p : infU E n → ℂ} (hp : p ∈ Algebra.adjoin ℂ (gens E n)) :
    ∃ N, p ∈ polys E n N := by
  have h : p ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) := hp
  rw [Algebra.adjoin_eq_span] at h
  clear hp
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := exists_mono_of_mem_closure hf
    exact ⟨l.length, Submodule.subset_span ⟨l, (le_refl l.length : l.length ≤ l.length), rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add f g _ _ hf hg =>
    obtain ⟨N, hN⟩ := hf
    obtain ⟨N', hN'⟩ := hg
    exact ⟨max N N', add_mem (polys_mono (le_max_left _ _) hN) (polys_mono (le_max_right _ _) hN')⟩
  | smul c f _ hf =>
    obtain ⟨N, hN⟩ := hf
    exact ⟨N, Submodule.smul_mem _ c hN⟩

theorem mono_mem_adjoin (l : List ((E →+* ℂ) × Fin n × Fin n)) : mono l ∈ Algebra.adjoin ℂ (gens E n) := by
  unfold mono
  induction l with
  | nil => simpa using one_mem (Algebra.adjoin ℂ (gens E n))
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (Algebra.subset_adjoin ⟨t.1, t.2.1, t.2.2, rfl⟩) ih

theorem polys_le_adjoin (N : ℕ) : polys E n N ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, rfl⟩; exact mono_mem_adjoin l)

def conjIdx (σ : ℂ ≃+* ℂ) (t : (E →+* ℂ) × Fin n × Fin n) : (E →+* ℂ) × Fin n × Fin n :=
  (σ.toRingHom.comp t.1, t.2)

theorem mono_conj (σ : ℂ ≃+* ℂ) (l : List ((E →+* ℂ) × Fin n × Fin n)) {γ : UA E n} (hγ : γ ∈ ratU E n)
    (k : infU E n) (hk : cInf k.1 = cInf γ) : mono (l.map (conjIdx σ)) k = σ (mono l k) := by
  induction l with
  | nil => simp [mono]
  | cons t l ih =>
    simp only [mono, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih, map_mul]
    congr 1
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk t.2.1 t.2.2
    simp only [gen, conjIdx, hx]
    rfl

theorem exists_conj_polys (σ : ℂ ≃+* ℂ) {N : ℕ} {p : infU E n → ℂ} (hp : p ∈ polys E n N) :
    ∃ p' ∈ polys E n N, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    exact ⟨mono (l.map (conjIdx σ)), Submodule.subset_span ⟨_, by simpa using hl, rfl⟩,
      fun γ hγ k hk => mono_conj σ l hγ k hk⟩
  | zero => exact ⟨0, zero_mem _, fun _ _ _ _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    exact ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => by
      rw [Pi.add_apply, Pi.add_apply, map_add, hf γ hγ k hk, hg γ hγ k hk]⟩
  | smul c f _ hf =>
    obtain ⟨f', hf', hf⟩ := hf
    exact ⟨σ c • f', Submodule.smul_mem _ _ hf', fun γ hγ k hk => by
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hf γ hγ k hk]⟩

theorem conj_span_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ),
    IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ),
      IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → φ' ∈ M := by
  intro E _ _ _ n φ hφ
  classical
  obtain ⟨hdense, hdk, -, a, b, -, -, hab, -⟩ := GlobalTheory.UnitarySplit.dense_and_split E n
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm E n φ hφ
  have hcont := (GlobalTheory.PolyRealU.poly_infU E n).1
  choose D hD using fun i => exists_polys_of_mem_adjoin (hpe i).1
  set N := Finset.univ.sup D with hN
  have hpN : ∀ i, p i ∈ polys E n N := fun i => polys_mono (Finset.le_sup (Finset.mem_univ i)) (hD i)
  set K := GlobalTheory.UnitaryDecomp.finStab φ with hK
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hφ.level
  set S' : Finset (UA E n) := S.image fun s => ((a s : finU E n) : UA E n) with hS'
  let M : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ K, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
        ∀ s ∈ S', (fun x : infU E n => ψ (s * x)) ∈ polys E n N}
      add_mem' := fun {ψ χ} hψ hχ =>
        ⟨fun γ hγ g => by simp only [Pi.add_apply, hψ.1 γ hγ g, hχ.1 γ hγ g],
          fun k hk g => by simp only [Pi.add_apply, hψ.2.1 k hk g, hχ.2.1 k hk g],
          fun s hs => add_mem (hψ.2.2 s hs) (hχ.2.2 s hs)⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => zero_mem _⟩
      smul_mem' := fun c ψ hψ =>
        ⟨fun γ hγ g => by simp only [Pi.smul_apply, hψ.1 γ hγ g],
          fun k hk g => by simp only [Pi.smul_apply, hψ.2.1 k hk g],
          fun s hs => Submodule.smul_mem _ c (hψ.2.2 s hs)⟩ }

  have hred : ∀ g : UA E n, ∃ s ∈ S', ∃ y : infU E n, ∀ ψ ∈ M, ψ g = ψ (s * y) := by
    intro g
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
    refine ⟨((a s : finU E n) : UA E n), by rw [hS']; exact Finset.mem_image_of_mem _ hs, ⟨(b s).1 * x, mul_mem (b s).2 hx⟩, fun ψ hψ => ?_⟩
    rw [hψ.2.1 k hk, mul_assoc, hψ.1 γ hγ]
    conv_lhs => rw [hab s]
    simp only [mul_assoc]
  haveI := polys_fd (E := E) (n := n) N
  let f : M →ₗ[ℂ] ((s : S') → polys E n N) :=
    { toFun := fun ψ s => ⟨fun x => ψ.1 (s.1 * x), ψ.2.2.2 s.1 s.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro ψ χ h
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, hs, y, hy⟩ := hred g
    rw [hy ψ.1 ψ.2, hy χ.1 χ.2]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨s, hs⟩)) y
  refine ⟨M, Module.Finite.of_injective f hinj, fun σ φ' hφ' hagree => ?_⟩

  have hrat : ∀ s ∈ finU E n, ∀ k : infU E n, ∀ γ ∈ ratU E n, cInf k.1 = cInf γ →
      φ' (s * (k : UA E n)) = σ (φ (s * (k : UA E n))) := by
    intro s hs k γ hγ hk
    have hy : γ⁻¹ * (s * (k : UA E n)) ∈ finU E n := by
      have hs1 : cInf s = 1 := hs
      show cInf (γ⁻¹ * (s * (k : UA E n))) = 1
      rw [map_mul, map_mul, map_inv, hs1, hk, one_mul, inv_mul_cancel]
    have e1 : s * (k : UA E n) = γ * (γ⁻¹ * (s * (k : UA E n))) := by group
    rw [e1, hφ'.left γ hγ, hφ.left γ hγ, hagree _ hy]
  refine ⟨hφ'.left, fun k hk => ?_, fun s hs => ?_⟩
  ·
    have hkφ : ∀ x, φ (x * (k : UA E n)) = φ x := fun x => congrFun hk x
    refine congrFun (Continuous.ext_on hdense (hφ'.cont.comp (continuous_mul_const _)) hφ'.cont ?_)
    rintro _ ⟨γ, hγ, x, hx, rfl⟩
    have hxk : x * (k : UA E n) ∈ finU E n := mul_mem hx k.2
    simp only [Function.comp_apply]
    rw [mul_assoc, hφ'.left γ hγ, hφ'.left γ hγ, hagree _ hxk, hagree _ hx, hkφ]
  · obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.1 hs
    have hsf : ((a s₀ : finU E n) : UA E n) ∈ finU E n := (a s₀).2
    choose p' hp'm hp' using fun i => exists_conj_polys σ (hpN i)
    have hq : (∑ i, σ (e i (a s₀)) • p' i) ∈ polys E n N :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hp'm i)
    convert hq using 1
    refine Continuous.ext_on hdk (hφ'.cont.comp (continuous_const.mul continuous_subtype_val))
      (hcont _ (polys_le_adjoin N hq)) ?_
    rintro k ⟨γ, hγ, hk⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrat _ hsf k γ hγ hk, hdec k, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hp' i γ hγ k hk, mul_comm]

end GlobalTheory.ConjSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra
section
noncomputable section

namespace GlobalTheory.CurveSigmaAlg

open NumberField Formalism.BasicNotions GlobalTheory.IsogConst

theorem hasCMBy_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨-, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0
  intro ω hω
  have h1 := hCM ω (by rw [← hL]; exact hω)
  rw [← hL] at h1
  have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
  rw [e]; exact h1

theorem secondEisensteinAlgebraic_of_invAlg : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  intro hInv D cc δ hcc hδ L hL
  obtain ⟨h2, h3⟩ := hInv D cc δ hcc hδ L hL
  have hcm := hasCMBy_curve D cc δ hcc hδ L hL
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d L hcm (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map Formalism.MainNotions.TaylorLogMetric.Qbar L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

end GlobalTheory.CurveSigmaAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal
section
noncomputable section

namespace GlobalTheory.TameEig

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology

theorem val_apply_eq {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h1 : A.valuation (σ y / y) = 1 := by
      have h2 := Valuation.map_add_eq_of_lt_left A.valuation (x := (1 : Ω)) (y := σ y / y - 1)
        (by rw [map_one]; exact hσ y hy)
      have e : (1 : Ω) + (σ y / y - 1) = σ y / y := by ring
      rwa [e, map_one] at h2
    have hv : A.valuation y ≠ 0 := by simpa using hy
    rw [map_div₀, div_eq_one_iff_eq hv] at h1
    exact h1

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv := val_apply_eq A σ hσ
  have hD : σ ∈ Dec (F := E) A := by
    rw [mem_Dec]
    ext x
    have e : x = σ • ((σ⁻¹ : G E Ω) • x) := (smul_inv_smul σ x).symm
    rw [e, ValuationSubring.smul_mem_pointwise_smul_iff, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def σ, hv]
  refine ⟨hD, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have e : σ x - x = x * (σ x / x - 1) := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) (hσ x h0)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem residue_eq_one (N : NData R H what₂) (i : N.Loc) {x : N.O i}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (N.O i)) : IsLocalRing.residue (N.O i) x = 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (N.O i)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hx

def chiBar (N : NData R H what₂) (i : N.Loc) : G H.E N.Om →* (IsLocalRing.ResidueField (N.O i))ˣ :=
  (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (N.chi i 1)

theorem chiBar_val (N : NData R H what₂) (i : N.Loc) (g : G H.E N.Om) :
    ((chiBar N i g : (IsLocalRing.ResidueField (N.O i))ˣ) : IsLocalRing.ResidueField (N.O i)) =
      IsLocalRing.residue (N.O i) (chi1 N i g) := rfl

theorem chiBar_open (N : NData R H what₂) (i : N.Loc) : IsOpen ((chiBar N i).ker : Set (G H.E N.Om)) := by
  have hm : IsOpen (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  let U1 : Set (G H.E N.Om) :=
    (fun g => ((N.chi i 1 g : (N.O i)ˣ) : N.O i) - 1) ⁻¹' (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i))
  have hU1 : IsOpen U1 := hm.preimage ((N.chi_cont i 1).sub continuous_const)
  have h1 : (1 : G H.E N.Om) ∈ U1 := by
    show ((N.chi i 1 1 : (N.O i)ˣ) : N.O i) - 1 ∈ IsLocalRing.maximalIdeal (N.O i)
    rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
  have hsub : U1 ⊆ ((chiBar N i).ker : Set (G H.E N.Om)) := by
    intro g hg
    show Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (N.chi i 1 g) = 1
    ext
    exact residue_eq_one N i hg
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU1.mem_nhds h1) hsub)

theorem not_isPrimePow_15 : ¬ IsPrimePow 15 := by
  intro h
  obtain ⟨p, k, hp, -, he⟩ := (isPrimePow_nat_iff 15).1 h
  have h3 : (3:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have h5 : (5:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
  have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5)
  omega

theorem residue_ne_one (N : NData R H what₂) (i : N.Loc)
    (w : PlE H) (hS : w ∈ N.S i) (q : ℕ) (hq : q.Prime) (hq15 : q % 15 = 1) (hw : w ∈ placesOver H.E q)
    (hDel : Nat.card ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) = 15) :
    IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)) ≠ 1 := by
  intro h1
  haveI : Fact q.Prime := ⟨hq⟩
  have hval : (N.plOm.1 w).valuation (q : N.Om) < 1 := by
    have := ((N.plOm.2 w) ((q : ℕ) : 𝓞 H.E)).2 hw
    simpa using this
  have hcop : Nat.Coprime 15 q :=
    (Nat.gcd_rec 15 q).trans (by simp only [hq15, Nat.gcd_one_left])
  have hpow : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), N.chi i 1 σ ^ 15 = 1 := by
    intro σ hσ
    have h := pow_card_eq_one' (G := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
      (x := ⟨N.chi i 1 σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [hDel] at h
    exact congrArg Subtype.val h
  have hwild : ∀ σ : G H.E N.Om, (∀ y : N.Om, y ≠ 0 → (N.plOm.1 w).valuation (σ y / y - 1) < 1) →
      σ ∈ (chiBar N i).ker := by
    intro σ hσ
    have hI := wild_mem_Ine (N.plOm.1 w) σ hσ
    have h15 : chiBar N i σ ^ 15 = 1 := by
      show (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom) (N.chi i 1 σ) ^ 15 = 1
      rw [← map_pow, hpow σ hI, map_one]
    exact GlobalTheory.T.character_trivial_at_wild_of_coprime_pow H.E N.Om q (N.plOm.1 w) hval _ (chiBar N i) (chiBar_open N i) σ
      (fun a ha => hσ a ha) 15 (by norm_num) hcop h15
  have hg : N.gam0 i w ∈ (chiBar N i).ker :=
    MonoidHom.mem_ker.2 (Units.ext (by simp only [chiBar_val, h1, Units.val_one]))
  have hTG := N.restN_tameGenerator_generates i w (Or.inl hS)
  have hle : ((Subgroup.closure (insert (N.gam0 i w) {σ : G H.E N.Om | ∀ y : N.Om, y ≠ 0 →
      (N.plOm.1 w).valuation (σ y / y - 1) < 1}) : Subgroup (G H.E N.Om)) : Set (G H.E N.Om)) ⊆
      ((chiBar N i).ker : Set (G H.E N.Om)) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hg, fun σ hσ => hwild σ hσ⟩)
  have hcl := Subgroup.isClosed_of_isOpen _ (chiBar_open N i)
  have hIne : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), IsLocalRing.residue (N.O i) (chi1 N i σ) = 1 := by
    intro σ hσ
    have h2 : σ ∈ (chiBar N i).ker := closure_minimal hle hcl (hTG.2 hσ)
    rw [← chiBar_val, MonoidHom.mem_ker.1 h2, Units.val_one]
  have : Finite ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hDel]; norm_num)
  obtain ⟨g, hgen⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
  obtain ⟨σ, hσ, hσg⟩ := Subgroup.mem_map.1 g.2
  have hord : orderOf (g : (N.O i)ˣ) = 15 := by rw [Subgroup.orderOf_coe, hgen, hDel]
  have hprim : IsPrimitiveRoot ((g : (N.O i)ˣ) : N.O i) 15 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf _
  apply GlobalTheory.T.primitiveRoot_notPrimePow_map_ne_one' _ (N.O i) (IsLocalRing.residue (N.O i)) _ 15 (by norm_num) hprim not_isPrimePow_15
  rw [← hσg]
  exact hIne σ hσ

theorem charpoly_red (N : NData R H what₂) {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))
    {w : PlE H} {x : N.X i} (hs : Formalism.MainNotions.SumRepresentations.SplitI N r w x) (γ : G H.E N.Om) (hγ : γ ∈ Ine (F := H.E) (N.plOm.1 w)) :
    ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      (X - 1) ^ R.r * (X - C (IsLocalRing.residue (N.O i) (chi1 N i γ))) ^ R.t := by
  have hK : (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly).map
      (algebraMap (N.O i) (Kf N i)) =
      ((X - 1) ^ R.r * (X - C (chi1 N i γ)) ^ R.t).map (algebraMap (N.O i) (Kf N i)) := by
    obtain ⟨Pm, hP⟩ := hs
    have h := hP γ hγ
    rw [← Matrix.charpoly_map]
    have e1 : ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (algebraMap (N.O i) (Kf N i)) =
        ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i)) := rfl
    have h2 := Matrix.charpoly_units_conj' Pm
      ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i))
    rw [← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, h] at h2
    rw [e1, ← h2]
    have h3 := Formalism.MainNotions.SumRepresentations.diagHom_charpoly (k := Kf N i) R.r R.t
      (Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom (N.chi i 1 γ))
    rw [Formalism.MainNotions.SumRepresentations.diagHom_coe] at h3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    exact h3
  have hO := Polynomial.map_injective _ (IsFractionRing.injective (N.O i) (Kf N i)) hK
  have e2 : ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) =
      ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (IsLocalRing.residue (N.O i)) := rfl
  rw [e2, Matrix.charpoly_map, hO]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_C]

theorem eigPd_holds : ∀ D : D7, SumRepresentations.AdmA D → LGC D → RbEx D → EigPd D := by
  intro D hA hLGC _ i _ w hS hw rb hrb hroot
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.2.2.2.2.2.2.2.2.1
  have hDel := Formalism.MainNotions.SumRepresentations.Del_holds D i
  have hq : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hq15 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) % 15 = 1 := by
    split_ifs
    · exact D.host.pde_mod.2
    · exact D.host.pde_mod.1
  have hne := residue_ne_one D.nd i w hS _ hq hq15 hw (hDel w hS hw)
  have hcond : w ∈ D.nd.Q i ∨ (Formalism.MainNotions.SumRepresentations.At.Del D.nd i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde'))) := by
    refine Or.inr ⟨hDel, ?_⟩
    by_cases hlp : D.nd.l i = D.host.pde
    · rw [if_pos hlp] at hw
      exact Or.inr ⟨hlp, hw⟩
    · rw [if_neg hlp] at hw
      exact Or.inl hw
  have x : D.nd.X i := Classical.choice (D.nd.neX i)
  have hQ : ∀ x, ∃ ρ, Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hA.2.2.1 i P
    obtain ⟨ρ, h1, h2, h3, -⟩ := GlobalTheory.T.exists_semisimple_galois_rep_weights D hA.1 hA.2.2.2.1 i P Pa hPa
    exact ⟨ρ, GlobalTheory.T.hecke_galois_of_unramified_match D i x P Pa hP hPa ρ h1 h2 h3⟩
  choose rq hrq using hQ
  obtain ⟨r, hr⟩ := Formalism.MainNotions.SumRepresentations.exists_GoodR D.nd D.naut hA.2.1 i ⟨rq, hrq⟩
  have hL := hLGC i r hr w (Or.inl hS)
  have hs := Formalism.MainNotions.SumRepresentations.split_inertia_of_hypotheses D.nd r D.naut hr hA.2.2.2.2.2.1 w (Or.inl hS) hcond hL x
  have hg := D.nd.locNd_chebotarevPlace_mem i w
  have hwl := D.nd.SQ_l i w (Or.inl hS)
  have fac := Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x (D.nd.gam0 i w)
  rw [charpoly_red D.nd r hs _ hg] at fac
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i c (D.nd.gam0 i w) : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ _c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))) :=
    Finset.prod_congr rfl fun c hc => by
      rw [Formalism.MainNotions.SumRepresentations.character_eq_first_off_l D.nd w hwl c (Finset.mem_Icc.1 hc).1 (Finset.mem_Icc.1 hc).2 _ hg]
      rfl
  rw [hprod, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at fac
  have hcp := mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) fac
  have h0 : ((X - 1 : Polynomial (IsLocalRing.ResidueField (D.nd.O i))) ^ D.R.r).eval
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) = 0 := by
    rw [← hcp]
    exact hroot
  rw [eval_pow, eval_sub, eval_X, eval_one] at h0
  exact pow_ne_zero _ (sub_ne_zero.2 hne) h0

end GlobalTheory.TameEig
end
end

