import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0153
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0154
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutForm
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_RU (x y : UA E n) (φ : UA E n → ℂ) : RU E n x (RU E n y φ) = RU E n (x * y) φ := by
  rw [map_mul]; rfl

theorem mem_infSpan (φ : UA E n → ℂ) (k : infU E n) : RU E n k φ ∈ infSpan φ :=
  Submodule.subset_span ⟨k, rfl⟩

theorem infSpan_stable (φ : UA E n → ℂ) (k : infU E n) : ∀ ψ ∈ infSpan φ, RU E n k ψ ∈ infSpan φ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l, rfl⟩ := h
    rw [RU_RU]
    exact mem_infSpan φ (k * l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c _ _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

def finStab (φ : UA E n → ℂ) : Subgroup (finU E n) where
  carrier := {k | RU E n k φ = φ}
  one_mem' := by
    change RU E n 1 φ = φ
    rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb => by
    change RU E n (a.1 * b.1) φ = φ
    rw [← RU_RU, show RU E n b φ = φ from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    change RU E n (a.1)⁻¹ φ = φ
    conv_lhs => rw [← show RU E n a φ = φ from ha]
    rw [RU_RU, inv_mul_cancel, map_one]; rfl

theorem isAutFormU_of_mem (hc : ∀ k : infU E n, ∀ g ∈ finU E n, k.1 * g = g * k.1) {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (ψ : UA E n → ℂ) (hψ : ψ ∈ infSpan φ) : IsAutFormU ψ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      exact hφ.cont.comp (continuous_mul_const l.1)
    | zero => exact continuous_const
    | add _ _ _ _ h₁ h₂ => exact h₁.add h₂
    | smul c _ _ h => exact h.const_smul c
  · intro γ hγ g
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      change φ (γ * g * l) = φ (g * l)
      rw [mul_assoc, hφ.left γ hγ]
    | zero => rfl
    | add _ _ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂]
    | smul c _ _ h => simp only [Pi.smul_apply, h]
  · refine Subgroup.isOpen_mono (H₁ := finStab φ) (H₂ := finStab ψ) (fun k hk => ?_) hφ.level
    change RU E n k ψ = ψ
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [RU_RU, ← hc l k.1 k.2, ← RU_RU, show RU E n k φ = φ from hk]
    | zero => rw [map_zero]
    | add _ _ _ _ h₁ h₂ => rw [map_add, h₁, h₂]
    | smul c _ _ h => rw [map_smul, h]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := infSpan φ) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact infSpan_stable φ k ψ hψ

def coeff (φ : UA E n → ℂ) (l : infSpan φ →ₗ[ℂ] ℂ) : infSpan φ →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun k => l.comp ((RU E n k).restrict (infSpan_stable φ k))

theorem continuous_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    Continuous fun k : infU E n => l ⟨RU E n k φ, mem_infSpan φ k⟩ := by
  have := hφ.kfin
  refine l.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun g => ?_) _)
  exact hφ.cont.comp (continuous_const.mul continuous_subtype_val)

theorem finite_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n =>
      l ⟨RU E n (x * k : infU E n) φ, mem_infSpan φ (x * k)⟩)) := by
  have := hφ.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coeff φ l)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨_, mem_infSpan φ k⟩, funext fun x => congrArg l (Subtype.ext ?_)⟩
  exact RU_RU x.1 k.1 φ

theorem exists_poly_mul_autForm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ)
    (hφ : IsAutFormU φ) : ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ),
      (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}
        ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  have := hφ.kfin
  let b := Module.finBasis ℂ (infSpan φ)
  refine ⟨_, fun i k => b.coord i ⟨RU E n k φ, mem_infSpan φ k⟩, fun i => (b i).1, fun i => ⟨?_, ?_⟩, fun k g => ?_⟩
  · exact GlobalTheory.UnitaryBC.rightFinite_mem_poly E n _ (continuous_coeff hφ _) (finite_coeff hφ _)
  · exact isAutFormU_of_mem (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.1 hφ _ (b i).2
  · have h := congrArg (fun v : infSpan φ => v.1 g) (b.sum_repr ⟨RU E n k φ, mem_infSpan φ k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm

end GlobalTheory.UnitaryDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqAndAlg
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomEq

theorem eq_and_alg : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) ∧ (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) :=
  ⟨fun _ _ _ B χ hcc hδ hχ => Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ,
   fun D cc δ B χ hcc hδ hχ => GlobalTheory.ThLoc.algTAll D cc δ B χ hcc hδ hχ⟩

end GlobalTheory.MomEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDefiniteUnitaryFunctionPolynomialMulSmooth
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem continuous_of_right_invariant_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G → ℂ) (V : Subgroup G) (hV : IsOpen (V : Set G)) (h : ∀ u ∈ V, ∀ g, e (g * u) = e g) :
    Continuous e := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open e).2 fun x => ?_)
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (V : Set G), hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← h _ hy x, mul_inv_cancel_left]

theorem exists_fun_of_poly_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU E n), IsOpen (V : Set (finU E n)) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU E n | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU E n) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  intro E _ _ _ n m p e hp he
  obtain ⟨-, -, -, a, b, ha, hb, -, hab⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨hcont, -, -, -, hco⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  choose V hVo hV using he
  have haf : ∀ g : finU E n, a g.1 = g := fun g => by simpa using (hab g 1).1
  have hbf : ∀ g : finU E n, b g.1 = 1 := fun g => by simpa using (hab g 1).2
  have hai : ∀ k : infU E n, a k.1 = 1 := fun k => by simpa using (hab 1 k).1
  have hbi : ∀ k : infU E n, b k.1 = k := fun k => by simpa using (hab 1 k).2
  have hR : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨fun x => ∑ i, p i (b x) * e i (a x), ?_, ?_, ?_, fun g k => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hcont _ (hp i)).comp hb).mul
      ((continuous_of_right_invariant_open _ _ (hVo i) (hV i)).comp ha)
  · set φ : UA E n → ℂ := fun x => ∑ i, p i (b x) * e i (a x) with hφ
    let S : Subgroup (finU E n) :=
      { carrier := {k : finU E n | RU E n k φ = φ}
        one_mem' := by
          change RU E n ((1 : finU E n) : UA E n) φ = φ
          funext g
          rw [hR]
          simp
        mul_mem' := fun {x y} hx hy => by
          change RU E n ((x * y : finU E n) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) g
          have h2 := congrFun (show RU E n y φ = φ from hy) (g * x)
          rw [hR] at h1 h2 ⊢
          rw [Subgroup.coe_mul, ← mul_assoc, h2, h1]
        inv_mem' := fun {x} hx => by
          change RU E n ((x⁻¹ : finU E n) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) (g * (x : UA E n)⁻¹)
          rw [hR] at h1 ⊢
          rw [Subgroup.coe_inv, ← h1, inv_mul_cancel_right] }
    have hle : (⨅ i, V i) ≤ S := fun u hu => by
      change RU E n (u : UA E n) φ = φ
      funext g
      rw [hR]
      simp only [hφ, map_mul, haf, hbf, mul_one]
      exact Finset.sum_congr rfl fun i _ => by rw [hV i u (Subgroup.mem_iInf.1 hu i)]
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hVo
  · choose N c d _ hcd using fun i => hco _ (hp i)
    let f : (Σ i, Fin (N i)) → UA E n → ℂ := fun s x => c s.1 s.2 (b x) * e s.1 (a x)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range f)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have : RU E n k (fun x => ∑ i, p i (b x) * e i (a x)) = ∑ s : Σ i, Fin (N i), d s.1 s.2 k • f s := by
      funext g
      rw [hR]
      simp only [map_mul, hai, hbi, mul_one, hcd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f,
        Fintype.sum_sigma, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    change RU E n k _ ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · simp only [(hab g k).1, (hab g k).2]

end GlobalTheory.UnitaryBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedEvaluationBranchingAllTuplesTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedEvaluation_branching_all_tuples_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), GlobalTheory.PerQ.LowerTieTwAt (I.rec7 l Z) (I.tw l l0 Z) u a := by
  first | exact @GlobalTheory.PerQ.lowerTieTwAt_all | exact GlobalTheory.PerQ.lowerTieTwAt_all | (intros; apply GlobalTheory.PerQ.lowerTieTwAt_all <;> assumption)
end

