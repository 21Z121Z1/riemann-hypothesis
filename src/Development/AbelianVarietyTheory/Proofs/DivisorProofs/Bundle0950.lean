import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSpanLeRapidSpan
section
open Classical MeasureTheory NumberField

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

theorem mspan_le_rspan : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  intro E _ _ _ a π
  refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF f hf => ?_,
    fun F hF r f => ?_⟩
  · obtain ⟨hk, he⟩ := GlobalTheory.T.archimedean_smooth_kernel_representation f hf
    rw [he F]
    exact kerInf_mem_rspan hF _ hk
  · have e : colConv r f F = kerInf (volume : Measure (Fin a → Cinf E)) (fun x => f x) (colU r) F := rfl
    rw [e]
    exact kerInf_mem_rspan hF _ (GlobalTheory.T.schwartz_rapid_decay_column r f)

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatMulAd

variable {D : D7}

theorem mulVec_map_mem_hatL {n : ℕ} (g : Matrix (Fin n) (Fin n) D.host.E)
    (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hg : ∀ x ∈ Λ, g *ᵥ x ∈ Λ') (y : Fin n → EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    g.map (eToEAf D) *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨g *ᵥ x, hg x hx, ?_⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have : g.map (eToEAf D) *ᵥ (r • a) = r • (g.map (eToEAf D) *ᵥ a) := by
      show _ = (r : EAf D) • (g.map (eToEAf D) *ᵥ a)
      rw [← Matrix.mulVec_smul]
      rfl
    rw [this]; exact Submodule.smul_mem _ r ha

theorem mem_hatL_colLat_mul (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E) : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  intro v
  have h1 : ∀ x ∈ colLat B, (γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat (γ * B) := by
    intro x hx
    rw [colLat_mul]
    exact ⟨x, hx, rfl⟩
  have h2 : ∀ x ∈ colLat (γ * B), ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat B := by
    intro x hx
    rw [colLat_mul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ y) ∈ _
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy
  constructor
  · intro hv
    exact mulVec_map_mem_hatL _ _ _ h2 v hv
  · intro hv
    have := mulVec_map_mem_hatL _ _ _ h1 _ hv
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec] at this

end GlobalTheory.LatMulAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKintIff
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isOpen_intR (r : ℕ) : IsOpen ((intR p K r : Subring (Kn p K r)) : Set (Kn p K r)) := by
  have h : ((intR p K r : Subring (Kn p K r)) : Set (Kn p K r)) =
      (Subtype.val : Kn p K r → PadicAlgCl p) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [intR, Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right]
    exact mem_Obar_iff
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

theorem mem_Kint_iff (n r : ℕ) (g : GL (Fin n) (Kn p K r)) :
    g ∈ Kint p K n r ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp [GeneralLinearGroup.map]
    · rw [← map_inv]
      simp [GeneralLinearGroup.map]
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hA : A.map (intR p K r).subtype = (g : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have hB : B.map (intR p K r).subtype = ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (intR p K r) => M.map (intR p K r).subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := by
      apply inj
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    have hBA : B * A = 1 := by
      apply inj
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

theorem isOpen_Kint : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ),
    IsOpen (Kint p K n r : Set (GL (Fin n) (Kn p K r))) := by
  intro p _ K n r
  have hS : IsOpen {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intR p K r).preimage ((continuous_apply j).comp (continuous_apply i))
  have hS' : IsOpen {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r} :=
    hS.preimage MulOpposite.continuous_unop
  have h : (Kint p K n r : Set (GL (Fin n) (Kn p K r))) = Units.embedProduct _ ⁻¹' (
      {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r} ×ˢ
      {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r}) := by
    ext g
    rw [SetLike.mem_coe, mem_Kint_iff]
    rfl
  rw [h]
  exact (hS.prod hS').preimage Units.continuous_embedProduct

end GlobalTheory.LKLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKintIffIntegralEntries
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem mem_intR_iff_norm_le_one (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)
    (x : Kn p K r) : x ∈ intR p K r ↔ ‖x‖ ≤ 1 := by
  change (x : PadicAlgCl p) ∈ Obar p ↔ _
  exact mem_Obar_iff

theorem mem_Kint_iff_integral_entries (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (g : GL (Fin n) (Kn p K r)) :
    g ∈ Kint p K n r ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) := by
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · change ((A : Matrix (Fin n) (Fin n) (intR p K r)) i j : Kn p K r) ∈ intR p K r
      exact SetLike.coe_mem _
    · rw [← map_inv]
      change (((A⁻¹ : GL (Fin n) (intR p K r)) : Matrix (Fin n) (Fin n) (intR p K r)) i j : Kn p K r) ∈ intR p K r
      exact SetLike.coe_mem _
  · rintro ⟨h1, h2⟩
    let B : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let C : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hB : B.map (intR p K r).subtype = (g : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have hC : C.map (intR p K r).subtype = ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (intR p K r) => M.map (intR p K r).subtype) := by
      intro M N h
      funext i j
      exact Subtype.ext (congrFun (congrFun h i) j)
    have hBC : B * C = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hB, hC, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have hCB : C * B = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hB, hC, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    refine ⟨⟨B, C, hBC, hCB⟩, ?_⟩
    ext i j
    rfl

theorem isCompact_Kint (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    (n r : ℕ) (hr : 0 < r) : IsCompact (Kint p K n r : Set (GL (Fin n) (Kn p K r))) := by
  haveI : FiniteDimensional ℚ_[p] (Kn p K r) := finiteDimensional_Kn p K hK hr
  haveI : ProperSpace (Kn p K r) := FiniteDimensional.proper ℚ_[p] (Kn p K r)
  set L := Kn p K r
  let Mset : Set (Matrix (Fin n) (Fin n) L) := {A | ∀ i j, A i j ∈ intR p K r}
  have hMset : Mset = Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : L) 1) := by
    ext A
    show (∀ i j, A i j ∈ intR p K r) ↔ _
    constructor
    · intro h i _ j _
      show A i j ∈ Metric.closedBall (0 : L) 1
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (mem_intR_iff_norm_le_one p K r _).1 (h i j)
    · intro h i j
      have h' : A i j ∈ Metric.closedBall (0 : L) 1 := h i trivial j trivial
      rw [Metric.mem_closedBall, dist_zero_right] at h'
      exact (mem_intR_iff_norm_le_one p K r _).2 h'
  have hM : IsCompact Mset := by
    rw [hMset]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hM' : IsCompact (MulOpposite.unop ⁻¹' Mset) := by
    have : MulOpposite.unop ⁻¹' Mset = MulOpposite.op '' Mset :=
      Set.ext fun x => ⟨fun h => ⟨x.unop, h, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact hy⟩
    rw [this]
    exact hM.image MulOpposite.continuous_op
  let S : Set (Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ) :=
    (Mset ×ˢ (MulOpposite.unop ⁻¹' Mset)) ∩ {x | x.1 * x.2.unop = 1} ∩ {x | x.2.unop * x.1 = 1}
  have hS : IsCompact S := by
    have hc1 : Continuous fun x : Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ => x.1 * x.2.unop :=
      continuous_fst.matrix_mul (MulOpposite.continuous_unop.comp continuous_snd)
    have hc2 : Continuous fun x : Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ => x.2.unop * x.1 :=
      (MulOpposite.continuous_unop.comp continuous_snd).matrix_mul continuous_fst
    exact ((hM.prod hM').inter_right (isClosed_eq hc1 continuous_const)).inter_right
      (isClosed_eq hc2 continuous_const)
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  convert hS using 1
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_Kint_iff_integral_entries p K n r u).1 hu
    exact ⟨⟨⟨h1, h2⟩, u.mul_inv⟩, u.inv_mul⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨x.1, x.2.unop, h3, h4⟩, (mem_Kint_iff_integral_entries p K n r _).2 ⟨h1, h2⟩, ?_⟩
    rfl

end GlobalTheory.LKLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffsStatement
section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  first | exact @GlobalTheory.JSW.Cut.cuts_mir_of_res | exact GlobalTheory.JSW.Cut.cuts_mir_of_res | (intros; apply GlobalTheory.JSW.Cut.cuts_mir_of_res <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotMove

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7} {T : Type} {A A' WW : HSp D}

def moveTri (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ) : Tri T A A' WW where
  rA := ⟨ΛA, Lev.finE A g * Y.rA.β, Y.rA.s, Y.rA.B⟩
  rA' := ⟨ΛA', Lev.finE A' g' * Y.rA'.β, Y.rA'.s, Y.rA'.B⟩
  rW := ⟨ΛW, Lev.finE WW h * Y.rW.β, Y.rW.s, Y.rW.B⟩
  ω := Y.ω
  ω' := Y.ω'
  vac := Y.ω t₀ (g, h) Y.vac
  vac' := Y.ω' t₀ (g', h) Y.vac'
  e := Y.e
  c := Y.c
  f t := (r t)⁻¹ • Y.ω t (g, h) (Y.f t)
  f' t := (r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)
  m := Y.m.map (fun x => x * g⁻¹)
  fd := (fun x => x * g) ⁻¹' Y.fd
  m' := Y.m'.map (fun x => x * g'⁻¹)
  fd' := (fun x => x * g') ⁻¹' Y.fd'

variable (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
  (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
  (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ)

theorem moveTri_lat : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ = ΛA ∧ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ = ΛA' ∧
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ = ΛW := ⟨rfl, rfl, rfl⟩

example : (moveTri Y ΛA ΛA' ΛW 1 1 1 t₀ (fun _ => 1) (fun _ => 1)).f = fun t => Y.ω t (1, 1) (Y.f t) := by
  funext t; simp [moveTri]

end GlobalTheory.BotMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0 := by
  first | exact @GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | exact GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | (intros; apply GlobalTheory.LowTypeDetermined.eq_zero_of_lowT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

section NabAux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

open Classical in

def colCoef {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) (ℓ : LtN Dw n) : k :=
  ∑ j : Fin n, if ℓ = ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ then B lam.1.1.1 lam.1.2 j else 0

theorem sum_colCoef_smul {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) {M : Type} [AddCommGroup M] [Module k M] (x : LtN Dw n → M) :
    ∑ ℓ, colCoef B cx lam ℓ • x ℓ =
      ∑ j : Fin n, B lam.1.1.1 lam.1.2 j • x ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ := by
  classical
  simp only [colCoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ : LtN Dw n)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem polyP_eq_aeval {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    polyP B cx = MvPolynomial.aeval (fun lam : Let cx => ∑ ℓ, MvPolynomial.C (colCoef B cx lam ℓ) *
      (MvPolynomial.X ℓ : MvPolynomial (LtN Dw n) k)) (polyH k cx) := by
  classical
  unfold polyP polyH
  rw [map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) (F := inferInstance) _ (by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, detPow, map_pow, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext1 a b
  simp only [GlobalTheory.CombMinor.cMat, Matrix.transpose_apply, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
    MvPolynomial.aeval_X, Function.comp_apply, MvPolynomial.C_mul']
  rw [sum_colCoef_smul]

theorem map_polyP {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    MvPolynomial.map φ (polyP B cx) = polyP (fun f b j => φ (B f b j)) cx := by
  unfold polyP
  rw [map_prod]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext1 a b
  simp [GlobalTheory.CombMinor.cMat]

theorem subst_colCoef_expPt {k : Type} [Field k] {v : AddValuation k (WithTop ℝ)} {d n : ℕ} (G : LogFGL v d)
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) (u : Lt1 Dw → Fin d → k) (Φ : PS k n d) :
    subst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ • (X lam : MvPowerSeries (Let cx) k))
      (subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
        (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) Φ) =
    subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ lam : Let cx,
      (B lam.1.1.1 lam.1.2 q.1 * u ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2⟩ e) •
        (X lam : MvPowerSeries (Let cx) k)) q.2) Φ := by
  have ht : HasSubst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ •
      (X lam : MvPowerSeries (Let cx) k)) := hasSubst_of_constantCoeff_zero (by simp)
  have hw : ∀ (j : Fin n) (e : Fin d), constantCoeff (∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = j then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) = 0 := by
    intro j e
    rw [map_sum]
    exact Finset.sum_eq_zero fun ℓ _ => by rw [constantCoeff_smul, constantCoeff_X, smul_zero]
  have hs : HasSubst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  refine (subst_comp_subst_apply hs ht Φ).trans (congrArg (fun s => subst s Φ) (funext fun q => ?_))
  refine (subst_expPt G ht (hw q.1) q.2).trans (congrArg (fun s => expPt G s q.2) (funext fun e => ?_))
  simp only [← coe_substAlgHom ht, map_sum, map_smul]
  simp only [coe_substAlgHom, subst_X ht, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := sum_colCoef_smul B cx lam
    (fun ℓ : LtN Dw n => if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0)
  simp only [smul_eq_mul] at h
  rw [Finset.sum_congr rfl fun ℓ _ => mul_comm _ _, h]
  simp

end NabAux

theorem nabSt_of : InvDerSt → LinSt → FrameSt → NabSt := by
  intro hI hL hF E _ _ _ H Dw l Xo c _ T io y Ch p _ X cx n B k g
  let _ := io.toAlgebra
  let _ : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hfr := (hF X.C (vX_vp X) (chD Ch.ch) T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).2.1 k
  have hinv := hI X.C (vX_vp X) (chD Ch.ch) (lawX Ch X) (fgl Ch X).F_int n (LtN Dw n) (fun ℓ => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx)) (g * frameX Ch X n ^ k)
  have hP : MvPolynomial.map X.ιF (polyT B cx) = polyP (fun f b j => jX X (B f b j)) cx := map_polyP _ _ _
  unfold nabX nabValN
  rw [hfr]
  refine Eq.trans hinv ?_
  rw [hP, polyP_eq_aeval, hL]
  exact congrArg (derivAt0 (polyH X.C cx))
    (subst_colCoef_expPt (fgl Ch X) (fun f b j => jX X (B f b j)) cx (lieVec Ch X) (g * frameX Ch X n ^ k))

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeDivisorsProdDistinctMonicIrreducible
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible

theorem exists_subset_natDegree_of_dvd_prod {k : Type} [Field k] {ι : Type} (P : ι → k[X])
    (hP : ∀ c, Irreducible (P c)) (s : Finset ι) :
    ∀ q : k[X], q ∣ ∏ c ∈ s, P c → ∃ A : Finset ι, A ⊆ s ∧ ∑ c ∈ A, (P c).natDegree = q.natDegree := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro q hq
    rw [Finset.prod_empty] at hq
    exact ⟨∅, Finset.Subset.refl _, by
      rw [Finset.sum_empty, natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hq)]⟩
  | insert i s hi ih =>
    intro q hq
    have hne : ∏ c ∈ insert i s, P c ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun c _ => (hP c).ne_zero
    have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero hne hq
    rw [Finset.prod_insert hi] at hq
    obtain ⟨q₁, q₂, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hq
    obtain ⟨A, hA, hsum⟩ := ih q₂ h2
    have hq1 : q₁ ≠ 0 := left_ne_zero_of_mul hq0
    have hq2 : q₂ ≠ 0 := right_ne_zero_of_mul hq0
    rw [natDegree_mul hq1 hq2]
    rcases (hP i).dvd_iff.mp h1 with hu | ha
    · exact ⟨A, hA.trans (Finset.subset_insert _ _), by
        rw [hsum, natDegree_eq_zero_of_isUnit hu, zero_add]⟩
    · refine ⟨insert i A, Finset.insert_subset_insert _ hA, ?_⟩
      rw [Finset.sum_insert (fun h => hi (hA h)), hsum,
        natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]

theorem natDegree_divisors_prod :
    ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  intro k _ ι _ P hP _
  refine ⟨fun a => ⟨?_, ?_⟩, fun Q => ⟨?_, ?_⟩⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨A, -, hA⟩ := exists_subset_natDegree_of_dvd_prod P (fun c => (hP c).2) _ q hq
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    exact ⟨∏ c ∈ A, P c, Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _),
      natDegree_prod_of_monic _ _ fun c _ => (hP c).1⟩
  · rintro ⟨q, hirr, hq, hQ⟩
    obtain ⟨c, -, hc⟩ := (Prime.dvd_finset_prod_iff hirr.prime _).mp hq
    have ha := hirr.associated_of_dvd (hP c).2 hc
    refine ⟨c, ?_⟩
    rwa [← natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]
  · rintro ⟨c, hc⟩
    exact ⟨P c, (hP c).2, Finset.dvd_prod_of_mem _ (Finset.mem_univ c), hc⟩

end GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormScalarPoincareDetRatioLactLeOneStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, ‖qS X x0 1 (lact γ x0)‖ ≤ 1 ∧ (‖qS X x0 1 (lact γ x0)‖ = 1 → ∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) := by
  first | exact @GlobalTheory.ScalarPoin.norm_qS_lact_le | exact GlobalTheory.ScalarPoin.norm_qS_lact_le | (intros; apply GlobalTheory.ScalarPoin.norm_qS_lact_le <;> assumption)
end

