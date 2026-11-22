import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLength
section
noncomputable section

namespace GlobalTheory.InertLatLength

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open GlobalTheory.LFun (toCompl latAt IsFrameAt)
open GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

def intMap (h : w.under (𝓞 F) = v) : intLoc F E v →+* w.adicCompletionIntegers E :=
  ((toCompl h).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E) fun y => toCompl_mem h y.2

theorem intMap_surjective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    Function.Surjective (intMap h) := by
  intro z
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2 (z : w.adicCompletion E)
  have hy' : y ∈ intLoc F E v := (mem_intLoc_iff hw h y).2 (by rw [hy]; exact z.2)
  exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩

def coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    Fin n → w.adicCompletion E :=
  (a⁻¹).1 *ᵥ (toCompl h ∘ y)

theorem mulVec_coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    a.1 *ᵥ coord h a y = toCompl h ∘ y := by
  rw [coord, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_latLoc_iff_coord {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)
    (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ ∀ i, coord h a y i ∈ w.adicCompletionIntegers E := by
  rw [mem_latLoc_iff hw h, ← mulVec_coord h a y]
  exact (ha _).symm

theorem coord_injective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) : Function.Injective (coord h a) := by
  intro y y' e
  have e' : toCompl h ∘ y = toCompl h ∘ y' := by rw [← mulVec_coord, ← mulVec_coord, e]
  exact funext fun i => (toCompl_bijective hw h).1 (congrFun e' i)

theorem coord_add (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y y' : Fin n → Fv F v ⊗[F] E) :
    coord h a (y + y') = coord h a y + coord h a y' := by
  simp only [coord, ← Matrix.mulVec_add]
  congr 1
  funext i
  simp [map_add]

theorem coord_smul (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (c : Fv F v ⊗[F] E)
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (fun i => c * y i) = toCompl h c • coord h a y := by
  simp only [coord, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem coord_mulVec (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (α : GL (Fin n) (Fv F v ⊗[F] E))
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (α.1 *ᵥ y) = (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ coord h a y := by
  rw [coord, comp_mulVec, ← mulVec_coord h a y, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Units.val_mul, Units.val_mul]

theorem exists_coord_eq (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) (z : Fin n → w.adicCompletion E) : ∃ y, coord h a y = z := by
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2.comp_left (a.1 *ᵥ z)
  refine ⟨y, ?_⟩
  rw [coord, show toCompl h ∘ y = a.1 *ᵥ z from hy, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

section Main

variable {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)

def phi : latLoc F L v →ₛₗ[intMap h] (Fin n → w.adicCompletionIntegers E) where
  toFun y i := ⟨coord h a y i, (mem_latLoc_iff_coord hw h ha y).1 y.2 i⟩
  map_add' y y' := funext fun i => Subtype.ext (congrFun (coord_add h a y y') i)
  map_smul' r y := funext fun i => Subtype.ext (congrFun (coord_smul h a r.1 y.1) i)

theorem coe_phi (y : latLoc F L v) (i : Fin n) : (phi hw h ha y i : w.adicCompletion E) = coord h a y i := rfl

include hw ha in
theorem phi_surjective : Function.Surjective (phi hw h ha) := by
  intro z
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun i => by rw [hy]; exact (z i).2
  exact ⟨⟨y, hm⟩, funext fun i => Subtype.ext (congrFun hy i)⟩

variable {M : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)} {α : GL (Fin n) (Fv F v ⊗[F] E)}

include hw ha in
theorem integral_entries (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) (i j : Fin n) :
    (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (Pi.single j 1)
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun k => by
    rw [hy]
    by_cases e : k = j
    · subst e; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne e]; exact zero_mem _
  have h1 := (mem_latLoc_iff_coord hw h ha _).1 (hM ((hα _).2 ⟨y, hm, rfl⟩)) i
  rw [coord_mulVec, hy, Matrix.mulVec_single_one] at h1
  exact h1

def intMat (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) :
    Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) :=
  Matrix.of fun i j => ⟨_, integral_entries hw h ha hM hα i j⟩

variable (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x)

theorem coe_intMat_mulVec (z : Fin n → w.adicCompletionIntegers E) (i : Fin n) :
    ((intMat hw h ha hM hα *ᵥ z) i : w.adicCompletion E) =
      ((a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ fun j => (z j : w.adicCompletion E)) i := by
  have := RingHom.map_mulVec (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα) z i
  exact this

theorem submoduleOf_eq :
    M.submoduleOf (latLoc F L v) = (LinearMap.range (intMat hw h ha hM hα).mulVecLin).comap (phi hw h ha) := by
  ext y
  change y.1 ∈ M ↔ _
  rw [hα, Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨phi hw h ha ⟨x, hx⟩, funext fun i => Subtype.ext ?_⟩
    rw [Matrix.mulVecLin_apply, coe_intMat_mulVec, coe_phi, e, coord_mulVec]
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
    have hm : x ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha x).2 fun i => by rw [hx]; exact (z i).2
    refine ⟨x, hm, coord_injective hw h a (funext fun i => ?_)⟩
    rw [coord_mulVec, hx, ← coe_intMat_mulVec hw h ha hM hα, ← coe_phi hw h ha y]
    exact congrArg (fun t => ((t i : w.adicCompletionIntegers E) : w.adicCompletion E)) hz.symm

def quotMap : (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) →ₛₗ[intMap h]
    ((Fin n → w.adicCompletionIntegers E) ⧸ LinearMap.range (intMat hw h ha hM hα).mulVecLin) :=
  (M.submoduleOf (latLoc F L v)).mapQ _ (phi hw h ha) (submoduleOf_eq hw h ha hM hα).le

theorem quotMap_bijective : Function.Bijective (quotMap hw h ha hM hα) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun q => ?_⟩
  · induction q using Submodule.Quotient.induction_on with
    | H y =>
      rw [quotMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero, submoduleOf_eq hw h ha hM hα]
      exact hq
  · induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨y, rfl⟩ := phi_surjective hw h ha z
      exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem length_eq_addVal :
    Module.length (intLoc F E v) (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) =
      IsDiscreteValuationRing.addVal _ (intMat hw h ha hM hα).det := by
  haveI : RingHomSurjective (intMap h) := ⟨intMap_surjective hw h⟩
  rw [← GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det, Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective (quotMap hw h ha hM hα) (quotMap_bijective hw h ha hM hα))

theorem coe_det_intMat :
    ((intMat hw h ha hM hα).det : w.adicCompletion E) = toCompl h (Matrix.GeneralLinearGroup.det α).1 := by
  have h1 := RingHom.map_det (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα)
  have h2 : (w.adicCompletionIntegers E).subtype.mapMatrix (intMat hw h ha hM hα) =
      (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 := Matrix.ext fun i j => rfl
  have h3 : Matrix.GeneralLinearGroup.det (a⁻¹ * Formalism.UG.bc (toCompl h) α * a) =
      Matrix.GeneralLinearGroup.det (Formalism.UG.bc (toCompl h) α) := by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  change (w.adicCompletionIntegers E).subtype _ = _
  rw [h1, h2]
  have h4 := congrArg Units.val h3
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply] at h4
  rw [h4, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Main

theorem ordL_eq_addVal {d : w.adicCompletionIntegers E} (hd : d ≠ 0) :
    ∃ m : ℕ, IsDiscreteValuationRing.addVal _ d = m ∧ Formalism.UG.ordL (d : w.adicCompletion E) = m := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ' : Valued.v ϖ = WithZero.exp (-1) := hϖ
  have hle : ϖ ∈ w.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  let π : w.adicCompletionIntegers E := ⟨ϖ, hle⟩
  have hπ := GlobalTheory.DegreeOneUniformiser.irreducible_of_valued w π hϖ'
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  refine ⟨m, IsDiscreteValuationRing.addVal_def d u hπ m hu, ?_⟩
  have hc : (d : w.adicCompletion E) = ((u : w.adicCompletionIntegers E) : w.adicCompletion E) * ϖ ^ m := by
    rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hv : Valued.v (d : w.adicCompletion E) = WithZero.exp (-(m : ℤ)) := by
    rw [hc, map_mul, map_pow, hϖ', HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit,
      one_mul, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hne : Valued.v (d : w.adicCompletion E) ≠ 0 := by rw [hv]; exact WithZero.exp_ne_zero
  have hz : WithZero.unzero hne = Multiplicative.ofAdd (-(m : ℤ)) :=
    WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, hv]; rfl)
  rw [Formalism.UG.ordL, dif_neg hne, hz]
  simp

theorem main_of_abs (habs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v), Formalism.UG.IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ,
    (absEv F E v x : ℝ) = (Formalism.UG.qV F v : ℝ) ^ (-(2 * Formalism.UG.ordL (toCompl h x.1)))) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ L _ v P hP g α hα
  have hw : Formalism.UG.IsInertAt F E v P := hP
  have h : P.under (𝓞 F) = v := (under_eq_iff hw P).2 rfl
  obtain ⟨a, ha⟩ := exists_isFrameAt hw (‹Submodule.IsLattice E L›.fg) (‹Submodule.IsLattice E L›.span_eq_top)
  have hM : latLoc F L v ⊓ latMoved σ J L v g ≤ latLoc F L v := inf_le_left
  have hα' : ∀ y, y ∈ latLoc F L v ⊓ latMoved σ J L v g ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x := fun y => hα y
  have hlen := length_eq_addVal hw h ha hM hα'
  have hdet := coe_det_intMat hw h ha hM hα'
  have hd0 : (intMat hw h ha hM hα').det ≠ 0 := by
    intro e
    rw [e, ZeroMemClass.coe_zero] at hdet
    exact ((Matrix.GeneralLinearGroup.det α).isUnit.map (toCompl h)).ne_zero hdet.symm
  obtain ⟨m, hm1, hm2⟩ := ordL_eq_addVal hd0
  refine ⟨m, hlen.trans hm1, ?_⟩
  have e1 := habs F E σ hσ v P h hw (Matrix.GeneralLinearGroup.det α)
  rw [← hdet, hm2] at e1
  have hq := absNorm_eq hσ.2.2.1 hw
  apply NNReal.eq
  rw [e1, NNReal.coe_zpow, hq, Formalism.UG.qV]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem absEv_det_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) :=
  main_of_abs GlobalTheory.AbsInert.absEv_inert

end GlobalTheory.InertLatLength
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsObj

open GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting hiding levJ

section Space

variable {D : D7}

theorem gramAt_posDef {V : HSp D} (hp : V.IsPosDef) (hs : V.SigOK) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have := hs (tauE D τ)
  rw [hp] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem exists_compact_of_fin (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hC : IsCompact C) : ∃ K : Set (GA D V), IsCompact K ∧ ∀ k : GA D V, (∀ i j, (finHom V k).1 i j ∈ C) → k ∈ K := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  choose R hR using fun τ => GlobalTheory.DefiniteQuotient.exists_bound_unitary (hV τ)
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k hk => hKe k fun i j => hCe' _ (hk i j) fun τ => ?_⟩
  have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
  have hu : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k) * V.gram.map (incA D) * Formalism.L2.Theta.mt V k = V.gram.map (incA D) := k.2
  have e : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k)).map ((θ τ).comp (infPart D)) =
      ((Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
    ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
  have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
  simp only [Matrix.map_mul, e, hJ] at this
  exact ((hR τ _ this i j).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))

theorem finite_stab (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V))
    {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)} (hC : IsCompact C) (hJ : ∀ k ∈ J, ∀ i j, k.1.1 i j ∈ C) (g : Bridge.Gf V) :
    Finite (Bridge.stab (Bridge.ratF V) J g) := by
  obtain ⟨-, -, h2, -, hg, hd, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_fin V hV hC
  obtain ⟨x, rfl⟩ := (finHom V).rangeRestrict_surjective g
  have hK' : IsCompact ((fun k => x * k * x⁻¹) '' K) := hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : GQ V → GA D V) ⁻¹' ((fun k => x * k * x⁻¹) '' K)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK').finite_of_discrete
  refine Set.Finite.subset hfin fun γ hγ => ⟨x⁻¹ * γ.1 * x, hKe _ ?_, by group⟩
  have h := hJ _ ((Bridge.mem_stab _).1 hγ)
  rw [map_mul, map_mul, map_inv]
  exact h

theorem exists_cover_of_compact {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) {C : Set G} (hC : IsCompact C)
    (hCe : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) :
    ∃ (m : ℕ) (c : Fin m → H), ∀ g, ∃ (a : Fin m) (γ : Γ) (k : J), g = π.comp Γ.subtype γ * c a * k := by
  obtain ⟨S, -, hS⟩ := hC.elim_nhds_subcover (fun x => {y | π (x⁻¹ * y) ∈ J}) fun x _ =>
    (ho.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp)
  refine ⟨_, fun a => π (S.equivFin.symm a).1, fun g => ?_⟩
  obtain ⟨x, rfl⟩ := hπ g
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hCe x
  obtain ⟨s, hs, hcs⟩ := Set.mem_iUnion₂.1 (hS hc)
  exact ⟨S.equivFin ⟨s, hs⟩, ⟨γ, hγ⟩, ⟨_, hcs⟩, by simp [mul_assoc]⟩

theorem exists_cover (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V)) (ho : IsOpenLev V J) :
    ∃ (m : ℕ) (c : Fin m → Bridge.Gf V), ∀ g, ∃ (a : Fin m) (γ : GQ V) (k : J), g = Bridge.ratF V γ * c a * k :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  (GlobalTheory.DefiniteQuotient.exists_compact V hV).elim fun _ h =>
    exists_cover_of_compact (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective J ho h.1 h.2

theorem isOpenLev_of_finCong (V : HSp D) {J : Subgroup (Bridge.Gf V)} {N : ℕ} (hN : 0 < N)
    (hK : ∀ k : GA D V, GlobalTheory.Member.FinCong V N k → fin V k ∈ J) : IsOpenLev V J := by
  obtain ⟨-, -, -, -, hg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN) hK)

theorem exists_split_system (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) {J : Subgroup (Bridge.Gf V)} {N₀ : ℕ} (hN₀ : 0 < N₀)
    (hK : ∀ k : GA D V, GlobalTheory.Member.FinCong V N₀ k → fin V k ∈ J) {N : ℕ} (hN : 0 < N) :
    ∃ (m : ℕ) (h : Fin m → GA D V), (∀ a, h a ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V (h a)).1) ∧
      Bridge.IsReps (Bridge.ratF V) J fun a => fin V (h a) := by
  obtain ⟨m, c, hc⟩ := exists_cover V hV J (isOpenLev_of_finCong V hN₀ hK)
  choose h hs he using fun a => GlobalTheory.SplitReps.exists_split_rep V hN₀ (fun k _ hk => hK k hk) hN (c a)
  have hr : Equivalence fun g g' : Bridge.Gf V => ∃ (γ : GQ V) (k : J), g = Bridge.ratF V γ * g' * k :=
    ⟨fun g => ⟨1, 1, by simp⟩, by
      rintro g g' ⟨γ, k, rfl⟩
      exact ⟨γ⁻¹, k⁻¹, by simp [mul_assoc]⟩, by
      rintro g g' g'' ⟨γ, k, rfl⟩ ⟨γ', k', rfl⟩
      exact ⟨γ * γ', k' * k, by simp [mul_assoc]⟩⟩
  obtain ⟨n, f, hf⟩ := GlobalTheory.UnRep.FullReps.exists_subfamily _ hr fun a => fin V (h a)
  refine ⟨n, fun a => h (f a), fun a => hs _, fun g => ?_⟩
  obtain ⟨a, ha⟩ := hc g
  exact hf g a (hr.trans ha (he a))

theorem finite_stab_of_le {V : HSp D} (hV : ∀ τ, (gramAt D V τ).PosDef) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Lat V}
    (hβ : IsSDFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {J : Subgroup (Bridge.Gf V)} (hle : J ≤ (levEnv V β L).J)
    (g : Bridge.Gf V) : Finite (Bridge.stab (Bridge.ratF V) J g) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  rw [← GlobalTheory.PrincInLevel.eq_latC hβ] at hfg hsp
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.StabCompact.exists_compact_entries D.host.F D.host.E Λ hfg hsp
  exact finite_stab V hV J hC (fun k hk => hCe _ fun y hy => GlobalTheory.RepsCompare.mulVec_mem_hat hβ L (hle hk) hy) g

end Space

section Levels

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T)

theorem exists_isBad {N : ℕ} (hN : 0 < N) : ∃ bad : ℕ, IsBad L t bad ∧ N ∣ bad := by
  classical
  refine ⟨N * ∏ PP ∈ L.Pg ∪ L.Q t, Ideal.absNorm PP.asIdeal, ⟨Nat.mul_pos hN (Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)), fun PP hPP => ?_⟩, dvd_mul_right _ _⟩
  obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) (Finset.mem_union.2 hPP)
  rw [hu, Nat.cast_mul, Nat.cast_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))

theorem exists_isAdReps (hβ : IsSDFrame (Vc D i) (L.βV i) (L.ΛV i) 1) (hp : (Vc D i).IsPosDef) {bad : ℕ} (hb : IsBad L t bad)
    {M : ℕ} (hM : 0 < M) : ∃ (n : ℕ) (h : Fin n → GA D (Vc D i)) (gam : Fin n → ℕ),
      IsSubLev (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) 1 ∧
      IsAdReps (Vc D i) (L.ΛV i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) bad (fun a => fin _ (h a))
        (fun a => Bridge.hLat (Vc D i) (fin _ (h a))) gam ∧
      IsLatReps (Vc D i) (L.ΛV i) bad (fun a => Bridge.hLat (Vc D i) (fin _ (h a))) ∧
      ∀ a, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * M) (finHom (Vc D i) (h a)).1 := by
  have hV := gramAt_posDef hp (D.sp.V_sig _)
  obtain ⟨n, h, h1, h2⟩ := exists_split_system (Vc D i) hV (J := GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) hb.1
    (fun k hk => GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Vc D i) (L.βV i) (L.ΛV i) (L.datVt i t) bad k hβ hb.2 hk)
    (Nat.mul_pos hb.1 hM)
  have H : IsAdReps (Vc D i) (L.ΛV i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) bad (fun a => fin _ (h a))
      (fun a => Bridge.hLat (Vc D i) (fin _ (h a))) _ :=
    ⟨h2, fun a => (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).2 (GlobalTheory.SplitReps.suppSplit_mono (dvd_mul_right _ _) (h1 a).2),
      fun a => (GlobalTheory.RepsCompare.isTransl_iff hβ _ _).2 rfl,
      fun a => ⟨finite_stab_of_le hV hβ (L.datVt i t) le_rfl _, rfl⟩⟩
  exact ⟨n, h, _, ⟨le_rfl, by simp, GlobalTheory.RepsCompare.isOpenLev_levEnv hβ (L.datVt i t) hb.1 hb.2, by simp⟩, H,
    GlobalTheory.RepsCompare.isLatReps_of_isAdReps hβ (L.datVt i t) le_rfl H, fun a => (h1 a).2⟩

theorem repsAt (hβ : IsSDFrame (Vc D i) (L.βV i) (L.ΛV i) 1) (hp : (Vc D i).IsPosDef) {N : ℕ} (hN : 0 < N) : RepsAt L i t N := by
  obtain ⟨bad, hb, hd⟩ := exists_isBad L t hN
  obtain ⟨n, h, gam, h1, h2, h3, -⟩ := exists_isAdReps L i t hβ hp hb one_pos
  exact ⟨n, _, _, bad, _, gam, 1, hb, hd, h1, h2, h3⟩

def RepsGeomAt {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (h : Fin n → Bridge.Gf (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ) (Lh : Fin n → Lat (Vc D i))
    (gam : Fin n → ℕ) (vol : ℝ) (La : Fin n → GenLat D.host.E (Vc D i).rank) (Nc : Fin n → ℕ),
    IsBad L t bad ∧ N ∣ bad ∧ IsSubLev (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) J' vol ∧
      IsAdReps (Vc D i) (L.ΛV i) J' bad h Lh gam ∧ IsLatReps (Vc D i) (L.ΛV i) bad Lh ∧
      RepsOK (l := l) bad La Nc gam ∧ LatPin Lh La

theorem isPosDef_of_vStd (hV : VStd D i) : (Vc D i).IsPosDef := fun τ => by
  have h := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) τ
  rw [GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hV, if_neg Bool.false_ne_true] at h
  rw [D.sp.V_rank _ (by omega) i.2]
  exact h

end Levels

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

def ChoiceWithReps (D : D7) : Prop :=
  ∀ C : Formalism.L2.Host.CharFrame D, ∃ L : LevCh D Unit, L.C = C ∧ L.Is () ∧
    ∀ (i : Fin D.R.m) (N : ℕ), 0 < N → RepsAt L i () N ∧
      ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), RepsGeomAt L i () l N

theorem row : Row := fun _ _ _ _ _ _ _ _ _ _ _ R hL hp i t _ hN => repsAt R.toLevCh i t (hL.βV i) (hp i) hN

section Record

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (K' : Type) [Field K']

def RepsEx : Prop :=
  ∀ (t : T0) (b : ℕ), 0 < b →
    ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ)
      (Lh : Cl → Lat (Vc D i)) (gam : Cl → ℕ) (vol : K'),
      RepsR R i t h bad J' Lh gam vol ∧ b ∣ bad ∧ (∀ k, 0 < gam k) ∧ vol ≠ 0

def RepsAll : Prop :=
  ∀ (t : T0) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))), bad ≠ 0 →
    (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → J' ≤ levJ R i t →
    IsOpen (J' : Set (Bridge.Gf (Vc D i))) →
    ∃ (n : ℕ) (h : Fin n → GA D (Vc D i)) (Lh : Fin n → Lat (Vc D i)) (gam : Fin n → ℕ) (vol : K'),
      RepsR R i t h bad J' Lh gam vol ∧ (∀ k, 0 < gam k) ∧ (CharZero K' → vol ≠ 0)

def RepsExCov : Prop :=
  ∀ {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
    {Tp : Type} (tup : Tp → T0) (dδ : Tp → DeltaDat Xo c (Vc D i).rank),
    ∃ (Cl : Tp → Type) (_ : ∀ t, Fintype (Cl t)) (h : ∀ t, Cl t → GA D (Vc D i))
      (J' : Tp → Subgroup (Bridge.Gf (Vc D i))) (bad : Tp → ℕ)
      (Lh : ∀ t, Cl t → Lat (Vc D i)) (gam : ∀ t, Cl t → ℕ) (vol : Tp → K')
      (La : ∀ t, Cl t → GenLat D.host.E (Vc D i).rank) (Nc : ∀ t, Cl t → ℕ),
      (∀ t, RepsR R i (tup t) (h t) (bad t) (J' t) (Lh t) (gam t) (vol t) ∧ vol t ≠ 0) ∧
      (∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1)) ∧
      RepsCov Xo c Cl dδ bad Lh La Nc gam

end Record

end GlobalTheory.RepsObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacter
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_isEig_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  intro k _ _ _ _ n χ V _ _ π hπ hχ v hv he
  obtain ⟨h1, h2⟩ := GlobalTheory.T.principalSeriesType_constant_family_det_character k n χ
  have hs : IsSmoothChar (detChar (Fin n) χ)⁻¹ := by
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) k → kˣ) :=
      Matrix.GeneralLinearGroup.continuous_det
    have ho : IsOpen ((χ.ker : Set kˣ)) := hχ
    have := ho.preimage hc
    unfold IsSmoothChar
    convert this using 1
    ext g
    simp [detChar, MonoidHom.mem_ker]
  have hk : twKer (twist π (detChar (Fin n) χ)⁻¹) (unipB k (Fin n)) 1 = twKer π (unipB k (Fin n)) 1 := by
    unfold twKer
    congr 1
    ext w
    refine exists_congr fun u => exists_congr fun x => ?_
    have hd : Matrix.GeneralLinearGroup.det (u : GL (Fin n) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    have : twist π (detChar (Fin n) χ)⁻¹ (u : GL (Fin n) k) x = π (u : GL (Fin n) k) x := by
      simp [twist, detChar, hd]
    rw [this]
  refine GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel k n V (twist π (detChar (Fin n) χ)⁻¹) (isSmooth_twist hπ hs) v (hk ▸ hv) ?_
  intro g hg
  have h3 := he g (by rw [h1]; exact hg)
  rw [h2 g hg] at h3
  show (((detChar (Fin n) χ)⁻¹ g : ℂˣ) : ℂ) • π g v = v
  rw [h3, smul_smul]
  simp

end GlobalTheory.PsType
end

