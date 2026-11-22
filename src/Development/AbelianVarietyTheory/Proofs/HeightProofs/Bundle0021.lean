import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TotallyPositiveExponents
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CuspFormNormData
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ImportsBis

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HermPartIsHermitian
section
noncomputable section

namespace GlobalTheory.CuspAlgComparison

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents
open Matrix hiding vec
open scoped ComplexOrder

section Host

variable {R : Ranks} (H : Host R)

theorem tau_injective : Function.Injective (tau H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

theorem tau_sqrt (τ : Pl R) : tau H τ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) :=
  ((factEmb R H).2 _).2 τ.2

theorem sqrt_d_pos : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)

theorem emb_cases (σ : H.E →+* ℂ) :
    ∃ τ : Pl R, σ = tau H τ ∨ σ = (starRingEnd ℂ).comp (tau H τ) := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  by_cases hg : g ∈ R.Psi
  · exact ⟨⟨g, hg⟩, Or.inl rfl⟩
  · rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, not_not] at hg
    refine ⟨⟨_, hg⟩, Or.inr (RingHom.ext fun x => ?_)⟩
    change H.emb g x = starRingEnd ℂ (H.emb (g * R.cc) x)
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    change _ = starRingEnd ℂ (H.emb g (H.conj x))
    rw [show H.emb g (H.conj x) = _ from H.conjE_apply _ x]
    simp

theorem tau_ne_conj (τ τ' : Pl R) : tau H τ ≠ (starRingEnd ℂ).comp (tau H τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h H.sqrtMinusD)
  rw [RingHom.comp_apply, tau_sqrt, tau_sqrt] at h1
  have := sqrt_d_pos H
  simp at h1
  linarith

end Host

section Forms

variable {R : Ranks} {H : Host R} {n : ℕ}

def mulR (c : Pl R → ℂ) (u : XR R n) : XR R n := fun τ i => c τ * u τ i

open Classical in
theorem sum_single_left (b : Pl R → Matrix (Fin n) (Fin n) ℂ) (τ : Pl R) (z : Fin n → ℂ) (v : XR R n) :
    ∑ τ', 2 * (star ((Pi.single τ z : XR R n) τ') ⬝ᵥ b τ' *ᵥ v τ').re = 2 * (star z ⬝ᵥ b τ *ᵥ v τ).re := by
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
  simp

end Forms

end GlobalTheory.CuspAlgComparison

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
section
open NumberField Matrix Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

namespace GlobalTheory.CuspCharLattice

section General

variable {K : Type} [Field K] [NumberField K]

theorem exists_smul_mem {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {M : Submodule (𝓞 K) W}
    {x : W} (hx : x ∈ Submodule.span K (M : Set W)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨⟨e, he⟩, b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) a
    refine ⟨d * e, mul_ne_zero hd (nonZeroDivisors.ne_zero he), ?_⟩
    have hb' : algebraMap (𝓞 K) K b = e • a := hb
    have : (d * e) • a • x = b • d • x := by
      rw [mul_smul, ← smul_assoc e a x, ← hb', algebraMap_smul, smul_comm]
    rw [this]
    exact M.smul_mem _ hx

theorem exists_den {n : ℕ} {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ M, ∀ i, d • x i ∈ (1 : Submodule (𝓞 K) K) := by
  classical
  obtain ⟨S, rfl⟩ := hM
  obtain ⟨⟨d, hd⟩, hy⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p => p.1 p.2)
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y h =>
    exact Submodule.mem_one.2 (hy _ (Finset.mem_image.2 ⟨(y, i), by simpa using h, rfl⟩))
  | zero => simp
  | add y z _ _ hy hz => rw [Pi.add_apply, smul_add]; exact add_mem hy hz
  | smul a y _ hy => rw [Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ _ hy

end General

variable {R : Ranks} {H : Host R} {n : ℕ}

theorem isLattice_dualZ (Y : Submodule (𝓞 H.E) (V H n))
    (h1 : ∀ i, ∃ c : H.E, c ≠ 0 ∧ (Pi.single i c : V H n) ∈ Y)
    (h2 : ∃ d : 𝓞 H.E, d ≠ 0 ∧ ∀ x ∈ Y, ∀ i, d • x i ∈ (1 : Submodule (𝓞 H.E) H.E)) :
    Submodule.IsLattice H.E (dualZ Y) := by
  classical
  refine ⟨?_, ?_⟩
  · choose c hc hcY using h1
    let J : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E := fun i =>
      FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton _ (c i))
    have hfg : (Submodule.pi Set.univ fun i => (J i : Submodule (𝓞 H.E) H.E)).FG :=
      Submodule.fg_pi fun i => FractionalIdeal.fg_of_isNoetherianRing le_rfl (J i)
    refine Submodule.FG.of_le hfg fun y hy i _ => ?_
    change y i ∈ J i
    rw [FractionalIdeal.mem_dual (FractionalIdeal.spanSingleton_ne_zero_iff.2 (hc i))]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
    obtain ⟨z, hz⟩ := hy _ (Y.smul_mem o (hcY i))
    refine ⟨z, ?_⟩
    rw [← Pi.single_smul, dotProduct_single] at hz
    rw [Algebra.traceForm_apply, hz]
    simp
  · obtain ⟨d, hd, h⟩ := h2
    have hd' : algebraMap (𝓞 H.E) H.E d ≠ 0 := by simpa using hd
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hm : (Pi.single i (algebraMap (𝓞 H.E) H.E d) : V H n) ∈ dualZ Y := by
      intro y hy
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h y hy i)
      rw [single_dotProduct, ← Algebra.smul_def, ← hb]
      have hi : IsIntegral ℤ (Algebra.trace ℚ H.E (algebraMap (𝓞 H.E) H.E b)) :=
        Algebra.isIntegral_trace b.2
      obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
      exact ⟨z, by rw [← hz]; simp⟩
    have : (Pi.single i (x i) : V H n) = (x i / algebraMap (𝓞 H.E) H.E d) •
        (Pi.single i (algebraMap (𝓞 H.E) H.E d) : V H n) := by
      rw [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ hd']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem isLattice_dualZ_idealMul (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) (h𝔞 : 𝔞 ≠ 0)
    (N : Submodule (𝓞 H.E) (V H n)) (hN : N.FG)
    (hs : ∀ v : V H n, ∃ d : 𝓞 H.E, d ≠ 0 ∧ d • v ∈ N) :
    Submodule.IsLattice H.E (dualZ (idealMul 𝔞 N)) := by
  classical
  refine isLattice_dualZ _ (fun i => ?_) ?_
  · obtain ⟨a, ha, ha0⟩ : ∃ a ∈ 𝔞, a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h𝔞 (FractionalIdeal.eq_zero_iff.2 hc)
    obtain ⟨d, hd, hv⟩ := hs (Pi.single i 1)
    have hd' : algebraMap (𝓞 H.E) H.E d ≠ 0 := by simpa using hd
    refine ⟨a * algebraMap (𝓞 H.E) H.E d, mul_ne_zero ha0 hd',
      Submodule.subset_span ⟨a, ha, _, hv, ?_⟩⟩
    rw [← Pi.single_smul, ← Pi.single_smul, Algebra.smul_def d, mul_one, smul_eq_mul]
  · obtain ⟨d, hd, h⟩ := exists_den hN
    obtain ⟨e, he, hA⟩ := 𝔞.isFractional
    refine ⟨e * d, mul_ne_zero (nonZeroDivisors.ne_zero he) hd, fun x hx i => ?_⟩
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hy
      obtain ⟨b, hb⟩ := hA a ha
      obtain ⟨b', hb'⟩ := Submodule.mem_one.1 (h v hv i)
      refine Submodule.mem_one.2 ⟨b * b', ?_⟩
      rw [map_mul, hb, hb', Pi.smul_apply, smul_eq_mul, smul_mul_smul_comm]
    | zero => simp
    | add y z _ _ hy hz => rw [Pi.add_apply, smul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ _ hy

theorem host_AA_ne_zero (H : Host R) : H.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact H.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := H.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

theorem isLattice_X : ∀ (D : Formalism.BasicNotions.D7) (j : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants.Lift D.R) (c : GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree.CuspGeom D j),
    Submodule.IsLattice D.host.E c.X := by
  intro D j c
  letI := D.host.cmStar
  have hl := c.lat_lat
  refine isLattice_dualZ_idealMul _ (host_AA_ne_zero D.host) c.N ?_ fun v => ?_
  · refine Submodule.fg_of_fg_map_injective (c.frame.restrictScalars (𝓞 D.host.E)) c.frame_inj ?_
    exact Submodule.FG.of_le hl.fg (Submodule.map_comap_le _ _)
  · obtain ⟨d, hd, h⟩ := exists_smul_mem (M := c.lat) (x := c.frame v) (by rw [hl.span_eq_top]; trivial)
    refine ⟨d, hd, ?_⟩
    change (c.frame.restrictScalars (𝓞 D.host.E)) (d • v) ∈ c.lat
    rw [map_smul]
    exact h

end GlobalTheory.CuspCharLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions
open scoped TensorProduct

namespace GlobalTheory.LatticeLocalGlobal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem repr_map {R R' ι : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

omit [NumberField E] in

theorem ext_components (z z' : Af F ⊗[F] E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z =
        Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z') : z = z' := by
  let b := Module.Basis.ofVectorSpace F E
  apply (Algebra.TensorProduct.basis (Af F) b).repr.injective
  refine Finsupp.ext fun k => FiniteAdeleRing.ext _ fun v => ?_
  have h1 := repr_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) b z k
  have h2 := repr_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) b z' k
  rw [h v, h2] at h1
  exact h1.symm

variable [StarRing E]

theorem exists_generators (V : HSpace E) :
    ∃ (k : ℕ) (x : Fin k → V.V), (∀ j, x j ∈ V.L0) ∧
      ∀ w ∈ V.L0, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j := by
  have := V.standardTuple_isLattice
  have : Module.Finite (𝓞 E) V.L0 := Module.Finite.iff_fg.2 V.standardTuple_isLattice.fg
  have : Module.Finite ℤ V.L0 := Module.Finite.trans (𝓞 E) V.L0
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := V.L0)
  refine ⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩
  have : (⟨w, hw⟩ : V.L0) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  refine ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this.symm

theorem exists_coeff (V : HSpace E) {k : ℕ} (x : Fin k → V.V)
    (hx : ∀ w ∈ V.L0, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin V.rank → Fv F v ⊗[F] E) (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v) :
    ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
      ∀ i, y i = ∑ j, a j ⊗ₜ[F] V.frame.repr (x j) i := by
  first
  | exact @_root_.GlobalTheory.MiscellaneousLemmas.main
  | exact _root_.GlobalTheory.MiscellaneousLemmas.main
  | (apply _root_.GlobalTheory.MiscellaneousLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MiscellaneousLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MiscellaneousLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MiscellaneousLemmas.main ..)

theorem mem_latHat_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
      (V : HSpace E) (y : Fin V.rank → Af F ⊗[F] E),
      y ∈ Formalism.MainNotions.StandardLattice.latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0} ↔
        ∀ v : HeightOneSpectrum (𝓞 F),
          (fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)) ∈
            GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  intro F E _ _ _ _ _ _ V y
  constructor
  · intro hy v
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨_, ha v, _, hx, ?_⟩
      funext i
      rw [V.frame.repr_sum_self]
      rfl
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, map_add]
      exact add_mem hy hz
    | neg y _ hy =>
      simp only [Pi.neg_apply, map_neg]
      exact neg_mem hy
  · intro h
    obtain ⟨k, x, hxL, hx⟩ := exists_generators V
    choose a ha ea using fun v => exists_coeff V x hx v _ (h v)
    let A : Fin k → Af F := fun j =>
      ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have hA : ∀ j v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (A j) = a v j := fun _ _ => rfl
    have e : y = ∑ j, fun i => A j ⊗ₜ[F] V.frame.repr (x j) i := by
      funext i
      apply ext_components
      intro v
      rw [ea v i, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.map_tmul, hA]
      rfl
    rw [e]
    refine sum_mem fun j _ => AddSubgroup.subset_closure
      ⟨A j, fun v => ha v j, fun i => V.frame.repr (x j) i, ?_, rfl⟩
    show ∑ i, V.frame.repr (x j) i • V.frame i ∈ V.L0
    rw [V.frame.sum_repr]
    exact hxL j

end GlobalTheory.LatticeLocalGlobal
end

