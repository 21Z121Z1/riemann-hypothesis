import Mathlib
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0147
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthFinsetSupEqSum
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory.CongruenceLengthSum

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

private theorem sep_lemma' {P₁ P₂ : Submodule O V} (hd : Disjoint P₁ P₂) {x₁ y₁ x₂ y₂ : V}
    (h₁ : x₁ ∈ P₁) (h₁' : y₁ ∈ P₁) (h₂ : x₂ ∈ P₂) (h₂' : y₂ ∈ P₂) (h : x₁ + x₂ = y₁ + y₂) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have e : x₁ - y₁ = y₂ - x₂ := by
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm y₁ y₂]
  have hz : x₁ - y₁ = 0 :=
    Submodule.disjoint_def.mp hd _ (sub_mem h₁ h₁') (e ▸ sub_mem h₂' h₂)
  have e1 : x₁ = y₁ := sub_eq_zero.mp hz
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact add_left_cancel h

theorem length_quot_sup (T₁ T₂ S₁ S₂ : Submodule O V) (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂)
    (hd : Disjoint T₁ T₂) :
    Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype) =
      Module.length O (↥T₁ ⧸ S₁.comap T₁.subtype) + Module.length O (↥T₂ ⧸ S₂.comap T₂.subtype) := by
  have key : ∀ a ∈ T₁, ∀ b ∈ T₂, a + b ∈ S₁ ⊔ S₂ ↔ a ∈ S₁ ∧ b ∈ S₂ := by
    intro a ha b hb
    constructor
    · intro h
      obtain ⟨s₁, hs₁, s₂, hs₂, hs⟩ := Submodule.mem_sup.mp h
      obtain ⟨e1, e2⟩ := sep_lemma' hd ha (h₁ hs₁) hb (h₂ hs₂) hs.symm
      rw [e1, e2]
      exact ⟨hs₁, hs₂⟩
    · rintro ⟨h1, h2⟩
      exact add_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  let f : (↥T₁ × ↥T₂) →ₗ[O] ↥(T₁ ⊔ T₂) :=
    LinearMap.codRestrict (T₁ ⊔ T₂) (T₁.subtype.coprod T₂.subtype)
      (fun p => add_mem (Submodule.mem_sup_left p.1.2) (Submodule.mem_sup_right p.2.2))
  let Φ := ((S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype).mkQ ∘ₗ f
  let Ψ : (↥T₁ × ↥T₂) →ₗ[O] (↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype) :=
    LinearMap.prodMap (S₁.comap T₁.subtype).mkQ (S₂.comap T₂.subtype).mkQ
  have hΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨y₁, y₂⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y₁
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y₂
    exact ⟨(a, b), rfl⟩
  have hker : LinearMap.ker Φ = LinearMap.ker Ψ := by
    ext ⟨a, b⟩
    simp only [LinearMap.mem_ker, Φ, Ψ, f, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.prodMap_apply, Prod.mk_eq_zero]
    exact key a a.2 b b.2
  calc Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype)
      = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Φ) :=
        (Φ.quotKerEquivOfSurjective hΦ).length_eq.symm
    _ = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Ψ) := (Submodule.quotEquivOfEq _ _ hker).length_eq
    _ = Module.length O ((↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype)) :=
        (Ψ.quotKerEquivOfSurjective hΨ).length_eq
    _ = _ := Module.length_prod _ _ _

theorem sup_inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (G₁ ⊔ G₂) ⊓ ((L₁ ⊔ L₂) ⊔ (B₁ ⊔ B₂)) = G₁ ⊓ (L₁ ⊔ B₁) ⊔ G₂ ⊓ (L₂ ⊔ B₂) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hc
    have e : g₁ + g₂ = (l₁ + b₁) + (l₂ + b₂) := by rw [← hyc]; abel
    obtain ⟨e1, e2⟩ := sep_lemma' hd (Submodule.mem_sup_left hg₁)
      (add_mem (hL₁ hl₁) (Submodule.mem_sup_right hb₁)) (Submodule.mem_sup_left hg₂)
      (add_mem (hL₂ hl₂) (Submodule.mem_sup_right hb₂)) e
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hg₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hg₂, ?_⟩))
    · rw [e1]
      exact add_mem (Submodule.mem_sup_left hl₁) (Submodule.mem_sup_right hb₁)
    · rw [e2]
      exact add_mem (Submodule.mem_sup_left hl₂) (Submodule.mem_sup_right hb₂)
  · refine sup_le (le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans ?_))
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans ?_))
    · exact sup_le_sup le_sup_left le_sup_left
    · exact sup_le_sup le_sup_right le_sup_right

theorem inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (L₁ ⊔ L₂) ⊓ (G₁ ⊔ G₂) = L₁ ⊓ G₁ ⊔ L₂ ⊓ G₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨e1, e2⟩ := sep_lemma' hd (hL₁ hl₁) (Submodule.mem_sup_left hg₁) (hL₂ hl₂)
      (Submodule.mem_sup_left hg₂) hg.symm
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hl₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hl₂, ?_⟩))
    · rw [e1]
      exact hg₁
    · rw [e2]
      exact hg₂
  · exact sup_le (inf_le_inf le_sup_left le_sup_left) (inf_le_inf le_sup_right le_sup_right)

end GlobalTheory.CongruenceLengthSum

open GlobalTheory.CongruenceLengthSum in

theorem GlobalTheory.congruence_length_finset_sup : ∀ (O V ι : Type) [CommRing O] [AddCommGroup V] [Module O V] (F : Finset ι) (L G B : ι → Submodule O V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → (∀ i ∈ F, L i ≤ G i ⊔ B i) → Module.length O (↥(F.sup G ⊓ (F.sup L ⊔ F.sup B)) ⧸ (F.sup L ⊓ F.sup G).comap (F.sup G ⊓ (F.sup L ⊔ F.sup B)).subtype) = ∑ i ∈ F, Module.length O (↥(G i ⊓ (L i ⊔ B i)) ⧸ (L i ⊓ G i).comap (G i ⊓ (L i ⊔ B i)).subtype) := by
  classical
  intro O V ι _ _ _ F L G B
  induction F using Finset.induction_on with
  | empty =>
    intro _ _ _
    rw [Finset.sum_empty, Module.length_eq_zero_iff]
    have : Subsingleton ↥((∅ : Finset ι).sup G ⊓ ((∅ : Finset ι).sup L ⊔ (∅ : Finset ι).sup B)) :=
      ⟨fun a b => Subtype.ext (by
        have ha := a.2
        have hb := b.2
        simp only [Finset.sup_empty, bot_sup_eq, inf_bot_eq, Submodule.mem_bot] at ha hb
        rw [ha, hb])⟩
    exact (Submodule.mkQ_surjective _).subsingleton
  | insert j F hj ih =>
    intro hSI hdis hL
    have hdj : Disjoint (G j ⊔ B j) (F.sup (fun i => G i ⊔ B i)) :=
      hSI (Finset.subset_insert j F) (Finset.mem_insert_self j F) hj
    replace hSI : F.SupIndep (fun i => G i ⊔ B i) := fun t ht i hi hit =>
      hSI (ht.trans (Finset.subset_insert j F)) (Finset.mem_insert_of_mem hi) hit
    have hGB : F.sup (fun i => G i ⊔ B i) = F.sup G ⊔ F.sup B := Finset.sup_sup (s := F) (f := G) (g := B)
    rw [hGB] at hdj
    have hLF : F.sup L ≤ F.sup G ⊔ F.sup B := Finset.sup_le fun i hi =>
      (hL i (Finset.mem_insert_of_mem hi)).trans (sup_le_sup (Finset.le_sup hi) (Finset.le_sup hi))
    have hLj : L j ≤ G j ⊔ B j := hL j (Finset.mem_insert_self j F)
    rw [Finset.sum_insert hj, Finset.sup_insert, Finset.sup_insert, Finset.sup_insert]
    rw [sup_inf_split _ _ _ _ _ _ hdj hLj hLF, inf_split _ _ _ _ _ _ hdj hLj hLF]
    have hS₁ : L j ⊓ G j ≤ G j ⊓ (L j ⊔ B j) := le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hS₂ : F.sup L ⊓ F.sup G ≤ F.sup G ⊓ (F.sup L ⊔ F.sup B) :=
      le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hT : Disjoint (G j ⊓ (L j ⊔ B j)) (F.sup G ⊓ (F.sup L ⊔ F.sup B)) :=
      hdj.mono (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_left)
    rw [length_quot_sup _ _ _ _ hS₁ hS₂ hT, ih hSI (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
      (fun i hi => hL i (Finset.mem_insert_of_mem hi))]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfContinuousTrace
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.SSCont

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem mem_imAlg_iff (r : Γ →* GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    x ∈ PI.SSAscent.UnitaryGroupMassFormula.imAlg r ↔
      x ∈ Submodule.span k (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) := by
  have h : (Submonoid.closure (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) :
      Set (Matrix (Fin n) (Fin n) k)) = Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) := by
    have e : (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) =
        (MonoidHom.mrange ((Units.coeHom _).comp r) : Set (Matrix (Fin n) (Fin n) k)) := by
      ext y
      simp
    rw [e, Submonoid.closure_eq]
  rw [PI.SSAscent.UnitaryGroupMassFormula.imAlg, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, h]

theorem exists_linear_of_trace [CharZero k] (r : Γ →* GL (Fin n) k) (hr : IsSSRep r) :
    ∃ (m : ℕ) (c : Fin m → Γ) (ψ : (Fin m → k) →ₗ[k] Matrix (Fin n) (Fin n) k),
      ∀ g, (r g : Matrix (Fin n) (Fin n) k) =
        ψ fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ n r hr
  set S : Set (Matrix (Fin n) (Fin n) k) := Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) with hS
  obtain ⟨f, hf, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k S
  choose c hc using hf
  let φ : Submodule.span k S →ₗ[k] (Fin (Module.finrank k (Submodule.span k S)) → k) :=
    LinearMap.pi fun i => (Matrix.traceLinearMap (Fin n) k k) ∘ₗ (LinearMap.mulRight k (f i)) ∘ₗ
      (Submodule.span k S).subtype
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    refine hnd x.1 ((mem_imAlg_iff r _).2 x.2) fun y hy => ?_
    have hy' := (mem_imAlg_iff r _).1 hy
    rw [← hS, ← hspan] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simpa [φ] using congrFun hx i
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul a y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ hφ
  refine ⟨_, c, (Submodule.span k S).subtype ∘ₗ ψ, fun g => ?_⟩
  let x : Submodule.span k S := ⟨r g, Submodule.subset_span ⟨g, rfl⟩⟩
  have h1 : (fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) = φ x := by
    funext i
    simp [φ, x, ← hc i]
  have h2 : ψ (φ x) = x := LinearMap.congr_fun hψ x
  rw [h1, LinearMap.comp_apply, h2]
  rfl

theorem continuous_of_continuous_trace : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsSSRep r → Continuous (fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → Continuous r := by
  intro Γ k _ _ _ _ _ _ _ n r hr ht
  obtain ⟨m, c, ψ, h⟩ := exists_linear_of_trace r hr
  have hc : Continuous fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [funext h]
    exact ψ.continuous_on_pi.comp (continuous_pi fun i => ht.comp (continuous_mul_const (c i)))
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  simp only [← map_inv]
  exact hc.comp continuous_inv

end GlobalTheory.SSCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyTestFunctionMulInverseUnitEqStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  first | exact @GlobalTheory.eventually_testFn_mul_inverse_eq | exact GlobalTheory.eventually_testFn_mul_inverse_eq | (intros; apply GlobalTheory.eventually_testFn_mul_inverse_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_sub_lin_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖w ^ k - 1 - k * (w - 1)‖ ≤ ‖w - 1‖ ^ 2 := by
  first
  | exact @_root_.GlobalTheory.UltrametricPowerBound.main
  | exact _root_.GlobalTheory.UltrametricPowerBound.main
  | (apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricPowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricPowerBound.main ..)

theorem exists_nat_norm_sub_le (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) :
    ∃ k : ℕ, ‖x - k‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
  let y : ℤ_[l] := ⟨x, hx⟩
  refine ⟨y.appr 1, ?_⟩
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 (y.appr_spec 1)
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
  simpa using h

theorem norm_pow_pow_sub_one (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (b : ℕ) :
    ‖u ^ (l ^ b) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have h := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj u hu ((l ^ b : ℕ) : ℤ) (by exact_mod_cast pow_ne_zero _ hl.ne_zero)
  rw [zpow_natCast, padicValInt.of_nat, padicValNat.prime_pow] at h
  rw [h]; push_cast; rfl

theorem exists_norm_sub_pow_le (j : ℕ) (hj : Lev l j) (u s : ℚ_[l]) (hu1 : ‖u‖ = 1)
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (hs : ‖s - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) (m : ℕ) :
    ∃ a : ℕ, ‖s - u ^ a‖ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  induction m with
  | zero => exact ⟨0, by simpa using hs⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    set w := u ^ (l ^ m) with hw
    have hw1 : ‖w‖ = 1 := by rw [hw, norm_pow, hu1, one_pow]
    have hd : ‖w - 1‖ = (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := norm_pow_pow_sub_one j hj u hu m
    have hdpos : 0 < ‖w - 1‖ := by rw [hd]; positivity
    have hd0 : w - 1 ≠ 0 := norm_pos_iff.1 hdpos
    set t := u ^ a with ht
    have ht1 : ‖t‖ = 1 := by rw [ht, norm_pow, hu1, one_pow]
    have ht0 : t ≠ 0 := norm_pos_iff.1 (by rw [ht1]; exact one_pos)
    obtain ⟨k, hk⟩ := exists_nat_norm_sub_le ((s - t) / (t * (w - 1))) (by
      rw [norm_div, norm_mul, ht1, one_mul, div_le_one hdpos, hd]; exact ha)
    refine ⟨a + l ^ m * k, ?_⟩
    have h : s - u ^ (a + l ^ m * k) = t * (w - 1) * ((s - t) / (t * (w - 1)) - k)
        + -(t * (w ^ k - 1 - k * (w - 1))) := by
      rw [pow_add, pow_mul, ← hw, ← ht]
      field_simp
      ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_mul, ht1, one_mul, hd]
      calc _ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) * (l : ℝ) ^ (-1 : ℤ) := by gcongr
        _ = _ := by
          rw [← zpow_add₀ hl0.ne']; congr 1; push_cast; ring
    · rw [norm_neg, norm_mul, ht1, one_mul]
      refine (norm_pow_sub_lin_le w hw1.le k).trans ?_
      rw [hd, ← zpow_natCast, ← zpow_mul]
      apply zpow_le_zpow_right₀ hl1.le
      have := hj.1
      push_cast; omega

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, (le_sup_left : K0 K ≤ Ks K j) x.2⟩

theorem gen_dense : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → (∃ g, IsGen χ K j g) ∧ ∀ g, IsGen χ K j g → ((∀ b : ℕ, IsGen χ K (j + b) (g ^ (l ^ b))) ∧ (∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n) ∧ (Gj K j : Set (GQ l)) ⊆ closure {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * g ^ a}) := by
  intro l _ act χ _ hχ K j hj
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hn, hcont, hG⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  refine ⟨?_, fun g hg => ?_⟩
  · have hp : ‖(l : ℚ_[l]) ^ j‖ = (l : ℝ) ^ (-(j : ℤ)) := by
      rw [norm_pow, Padic.norm_p]; simp
    have hlt : ‖(l : ℚ_[l]) ^ j‖ < 1 := by
      rw [hp]; apply zpow_lt_one_of_neg₀ hl1; have := hj.1; omega
    have hu : ‖(1 : ℚ_[l]) + (l : ℚ_[l]) ^ j‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'),
        norm_one, max_eq_left hlt.le]
    obtain ⟨g, hg0, hg⟩ := (GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective l K).2 χ hχ _ hu
    have : ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by rw [hg, add_sub_cancel_left, hp]
    exact ⟨g, ((hG K g hg0).1 j).2 this.le, this⟩
  have hg0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hg.1
  have hcos : ∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n := by
    intro σ hσ n
    have hσ0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hσ
    obtain ⟨a, ha⟩ := exists_norm_sub_pow_le j hj _ _ (hn g) hg.2 (((hG K σ hσ0).1 j).1 hσ) n
    refine ⟨a, ((hG K _ (mul_mem hσ0 (inv_mem (pow_mem hg0 a)))).1 n).2 ?_⟩
    have h0 : (χ g : ℚ_[l]) ≠ 0 := Units.ne_zero _
    have h : ((χ (σ * (g ^ a)⁻¹) : ℚ_[l]ˣ) : ℚ_[l]) - 1
        = ((χ σ : ℚ_[l]) - (χ g : ℚ_[l]) ^ a) / (χ g : ℚ_[l]) ^ a := by
      simp only [map_mul, map_inv, map_pow, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val]
      field_simp
    rw [h, norm_div, norm_pow, hn, one_pow, div_one]
    refine ha.trans (zpow_le_zpow_right₀ hl1.le ?_)
    push_cast; omega
  refine ⟨fun b => ?_, hcos, fun σ hσ => ?_⟩
  · have : ‖(χ (g ^ (l ^ b)) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
      rw [map_pow, Units.val_pow_eq_pow_val]
      exact norm_pow_pow_sub_one j hj _ hg.2 b
    exact ⟨((hG K _ (pow_mem hg0 _)).1 _).2 this.le, this⟩
  · rw [mem_closure_iff]
    intro U hU hσU
    have hW : IsOpen (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) :=
      isOpen_biUnion fun h _ => hU.preimage (by fun_prop)
    have hcl : ∀ n : ℕ, IsClosed (Gj K n : Set (GQ l)) := fun n =>
      InfiniteGalois.fixingSubgroup_isClosed _
    have hanti : Antitone fun n : ℕ => (Gj K n : Set (GQ l)) := by
      intro m n hmn x hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K n hx
      refine ((hG K x hx0).1 m).2 ((((hG K x hx0).1 n).1 hx).trans
        (zpow_le_zpow_right₀ hl1.le (by omega)))
    have hint : ∀ x ∈ ⋂ n : ℕ, (Gj K n : Set (GQ l)),
        (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) ∈ nhds x := by
      intro x hx
      rw [Set.mem_iInter] at hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K 0 (hx 0)
      have hxH : x ∈ Hinf K := by
        refine (hG K x hx0).2.2 (Units.ext ?_)
        rw [Units.val_one, ← sub_eq_zero, ← norm_le_zero_iff]
        by_contra hne
        obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (not_le.1 hne) (inv_lt_one_of_one_lt₀ hl1)
        have := ((hG K x hx0).1 n).1 (hx n)
        rw [zpow_neg, zpow_natCast, ← inv_pow] at this
        linarith
      exact hW.mem_nhds (Set.mem_biUnion hxH (by simpa using hσU))
    obtain ⟨n, hn'⟩ := exists_subset_nhds_of_compactSpace hanti.directed_ge hcl
      hint
    obtain ⟨a, ha⟩ := hcos σ hσ n
    obtain ⟨h, hh, hU'⟩ := Set.mem_iUnion₂.1 (hn' ha)
    refine ⟨h * g ^ a, ?_, h, hh, a, rfl⟩
    simpa [mul_assoc] using hU'

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLeftInverseOfPhiModuleExactTriple
section
open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK.IntegralLeftInverseExactTriple

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem mem_M_single (P : PhiMod O K l e a ι) (τ : ZMod a) (u : ι → K⟦X⟧)
    (hu : ∀ i, u i ∈ A O K) : (Pi.single τ u : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun σ => mem_vecs.2 fun i => ?_
  by_cases h : σ = τ
  · subst h; simpa using hu i
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem app_single {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (τ : ZMod a)
    (u : ι → K⟦X⟧) : F.app (Pi.single τ u) = Pi.single τ (F.mat τ *ᵥ u) := by
  funext σ
  rw [Hom.app_apply]
  by_cases h : σ = τ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem smul_one_mem (ν : Type) [Fintype ν] [DecidableEq ν] (n : ℕ) (i j : ν) :
    (((l : K) ^ n) • (1 : Matrix ν ν K⟦X⟧)) i j ∈ A O K := by
  rw [Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · rw [show ((l : K) ^ n) • (1 : K⟦X⟧) = ((l ^ n : ℕ) : K⟦X⟧) by simp [Algebra.smul_def]]
    exact natCast_mem _ _
  · rw [smul_zero]; exact zero_mem _

end GlobalTheory.BK.IntegralLeftInverseExactTriple

namespace GlobalTheory.BK

open IntegralLeftInverseExactTriple in

theorem exists_integral_leftInverse_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : GlobalTheory.BK.Hom P Q) (G : GlobalTheory.BK.Hom Q T), IsExactTriple F G → ∀ n : ℕ, (∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) → ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧) := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG n hG τ
  have h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ) :=
    fun j => hG _ (mem_M_single T τ _ fun i => by
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
  choose x hxM hx using h1
  let Xm : Matrix κ μ K⟦X⟧ := Matrix.of fun k j => x j τ k
  have hXA : ∀ k j, Xm k j ∈ A O K := fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k
  have hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hx j) τ) i
    rw [Hom.app_apply, Pi.smul_apply, Pi.single_eq_same] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm] using this
  have hGF : G.mat τ * F.mat τ = 0 := by
    refine Matrix.ext fun i j => ?_
    have hs := mem_M_single P τ (Pi.single j 1) fun i' => by
      by_cases h : i' = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 := (hFG.exact _ (F.app_mem_M hs)).2 ⟨_, hs, rfl⟩
    have := congrFun (congrFun h0 τ) i
    rw [app_single, app_single, Pi.single_eq_same, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
      at this
    simpa using this
  let Z : Matrix κ κ K⟦X⟧ := ((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ
  have hZA : ∀ k k', Z k k' ∈ A O K := fun k k' => sub_mem (smul_one_mem κ n k k')
    (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))
  have hGZ : G.mat τ * Z = 0 := by
    simp only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX,
      Matrix.smul_mul, Matrix.one_mul, sub_self]
  have h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k) := by
    intro k
    have hm := mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k
    have hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0 := by
      funext i
      have := congrFun (congrFun hGZ i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    obtain ⟨w, hw, h⟩ := (hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])
    exact ⟨w, hw, h⟩
  choose w hwM hw using h2
  let W : Matrix ι κ K⟦X⟧ := Matrix.of fun i k => w k τ i
  have hWA : ∀ i k, W i k ∈ A O K := fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i
  have hFW : F.mat τ * W = Z := by
    refine Matrix.ext fun i k => ?_
    have := congrFun (congrFun (hw k) τ) i
    rw [Hom.app_apply, Pi.single_eq_same] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  refine ⟨W, hWA, ?_⟩
  have hFWF : F.mat τ * (W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hFW]
    simp only [Z, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hGF,
      Matrix.mul_zero, sub_zero, Matrix.mul_smul, Matrix.mul_one, sub_self]
  rw [← sub_eq_zero]
  refine Matrix.ext fun i j => ?_
  set D := W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧) with hD
  have hDm : Pi.single τ (fun i' => D i' j) ∈ P.M := mem_M_single P τ _ fun i' =>
    sub_mem (Subalgebra.sum_mem _ fun k _ => mul_mem (hWA i' k) (F.mem _ _ _)) (smul_one_mem ι n i' j)
  have hFD : F.mat τ *ᵥ (fun i' => D i' j) = 0 := by
    funext k
    have := congrFun (congrFun hFWF k) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h0 := hFG.inj _ hDm (by rw [app_single, hFD, Pi.single_zero])
  have := congrFun (congrFun h0 τ) i
  simpa using this

end GlobalTheory.BK
end

