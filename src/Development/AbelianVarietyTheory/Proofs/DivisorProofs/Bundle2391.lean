import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoClassifyingOfInjectiveFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDenominator
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory.Cartier

namespace GlobalTheory.DenominatorExistenceLemmas

variable {M W : Scheme.{0}}

theorem finite_app (f : M ⟶ W) [IsProper f] [IsLocallyNoetherian W] {L : ReciprocityTheory.ChartRestriction.G.Semi.LB M}
    (hL : IsAmpleLB L) {V : W.Opens} (hV : IsAffineOpen V) : (f.app V).hom.Finite := by
  obtain ⟨_, hfa⟩ := GlobalTheory.ProperFinite.isFiniteQC_pushforward f hL (structureModule M)
  exact hfa V hV

variable [IsIntegral M] [IsIntegral W]

omit [IsIntegral W] in

theorem gen_mem_preimage (f : M ⟶ W) [IsDominant f] {U : W.Opens} {y : W} (hy : y ∈ U) :
    genericPoint M ∈ f ⁻¹ᵁ U := by
  obtain ⟨m, hm⟩ := f.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
  exact gen_mem (U := f ⁻¹ᵁ U) (x := m) hm

omit [IsIntegral W] in

theorem fnOf_map {U V : M.Opens} (e : V ≤ U) (h : genericPoint M ∈ V) (a : Γ(M, U)) :
    fnOf V h (M.presheaf.map (homOfLE e).op a) = fnOf U (e h) a := by
  exact fnOf_resG e h a

theorem exists_denominator {V : W.Opens} (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) {ι : Type} [Finite ι]
    (c : ι → W.functionField) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ i, ∃ a : Γ(W, V), fnOf V hg a = fnOf V hg d * c i := by
  have : Nonempty V := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen W V hV
  obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(W, V)) c
  refine ⟨d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hdc i
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def] at ha
  exact ha

theorem exists_denominator_all (f : M ⟶ W) [IsDominant f] {V : W.Opens} (hV : IsAffineOpen V)
    (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) (hf : (f.app V).hom.Finite) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ j (b : Γ(M, f ⁻¹ᵁ V)), ∃ a : Γ(W, V),
      fnOf V hg a = fnOf V hg d * co j (fnOf (f ⁻¹ᵁ V) hg' b) := by
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(W, V) Γ(M, f ⁻¹ᵁ V) := hf
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(W, V)) (M := Γ(M, f ⁻¹ᵁ V))
  obtain ⟨d, hd0, hd⟩ := exists_denominator hV hg
    (fun p : Fin r × Fin n => co p.1 (fnOf (f ⁻¹ᵁ V) hg' (s p.2)))
  refine ⟨d, hd0, fun j b => ?_⟩
  have hb : b ∈ Submodule.span Γ(W, V) (Set.range s) := hs ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hd (j, k)
  | zero => exact ⟨0, by simp only [map_zero, mul_zero]⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hx'
    exact ⟨a + a', by rw [map_add, map_add, map_add, ha, ha', mul_add]⟩
  | smul t x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨t * a, ?_⟩
    have ht : fnOf (f ⁻¹ᵁ V) hg' (t • x) = functionFieldMap f (fnOf V hg t) * fnOf (f ⁻¹ᵁ V) hg' x := by
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra]
      congr 1
      exact GlobalTheory.Cartier.DomPull.fnOf_app f hg' t
    rw [ht, hco, map_mul, ha]
    ring

theorem exists_pow_mul_eq (f : M ⟶ W) [IsDominant f] [QuasiCompact f] [QuasiSeparatedSpace M] {V : W.Opens}
    (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) {y : W} (hy : y ∈ V)
    {V' : W.Opens} (hy' : y ∈ V') (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) :
    ∃ (u : W.functionField) (b : Γ(M, f ⁻¹ᵁ V)), UnitAt y u ∧
      fnOf (f ⁻¹ᵁ V) hg' b = functionFieldMap f u * fnOf (f ⁻¹ᵁ V') h z := by
  obtain ⟨g, hgV', hyg⟩ := hV.exists_basicOpen_le ⟨y, hy'⟩ hy
  have hle : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V' := by
    rw [← Scheme.preimage_basicOpen]
    exact fun x hx => hgV' hx
  have hgb : genericPoint M ∈ M.basicOpen (f.app V g) := by
    rw [← Scheme.preimage_basicOpen]
    exact gen_mem_preimage f hyg
  obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated M (f ⁻¹ᵁ V)
    (f.isCompact_preimage hV.isCompact) (IsQuasiSeparated.of_quasiSeparatedSpace _) (f.app V g) (M.presheaf.map (homOfLE hle).op z)
  have e0 : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V := M.basicOpen_le _
  have h1 : fnOf _ hgb (M.presheaf.map (homOfLE e0).op b) =
      fnOf _ hgb (M.presheaf.map (homOfLE e0).op (f.app V g)) ^ n *
        fnOf _ hgb (M.presheaf.map (homOfLE hle).op z) := by
    rw [← map_pow, ← map_mul]
    exact congrArg _ hb
  rw [fnOf_map, fnOf_map, fnOf_map] at h1
  refine ⟨fnOf V hg g ^ n, b, ?_, ?_⟩
  · have hu : UnitAt y (fnOf V hg g) := (unitAt_fnOf_iff hy hg g).2 hyg
    clear h1 hb
    induction n with
    | zero => simpa using unitAt_one y
    | succ n ih => rw [pow_succ]; exact ih.mul hu
  · rw [map_pow, ← GlobalTheory.Cartier.DomPull.fnOf_app f hg' g]
    exact h1

omit [IsIntegral M] [IsIntegral W] in

theorem exists_local_denominator (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    [IsProper f] [IsLocallyNoetherian W] (L : ReciprocityTheory.ChartRestriction.G.Semi.LB M) (hL : IsAmpleLB L) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) (y : W) :
    ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧
      ∀ y' ∈ V, ∀ V' : W.Opens, y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r),
        RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  obtain ⟨V, hVa, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian f
  have : TopologicalSpace.NoetherianSpace M := GlobalTheory.IsAmpleLB.noetherianSpace hL
  have hg' : genericPoint M ∈ f ⁻¹ᵁ V := gen_mem_preimage f hyV
  obtain ⟨d, hd0, hd⟩ := exists_denominator_all f hVa (gen_mem hyV) hg' (finite_app f hL hVa) co hco
  refine ⟨V, hyV, d, hd0, fun y' hy'V V' hy'V' h z j => ?_⟩
  obtain ⟨u, b, hu, hb⟩ := exists_pow_mul_eq f hVa (gen_mem hyV) hg' hy'V hy'V' h z
  obtain ⟨a, ha⟩ := hd j b
  have hz : fnOf (f ⁻¹ᵁ V') h z = functionFieldMap f u⁻¹ * fnOf (f ⁻¹ᵁ V) hg' b := by
    rw [hb, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu.ne_zero, map_one, one_mul]
  rw [hz, hco, mul_left_comm (fnOf V (gen_mem hyV) d), ← ha]
  exact hu.inv.regAt.mul (regAt_fnOf hy'V _ a)

end GlobalTheory.DenominatorExistenceLemmas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FibreBasisSpread

theorem exists_away_linearCombination_bijective : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  intro R _ M _ _ _ _ J _ v p _ hbij
  classical
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p
  have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (Finsupp.mapRange.linearMap (Algebra.linearMap R Rp)) (TensorProduct.mk R Rp M 1)
      (Finsupp.linearCombination R v)) := by
    rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [← (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).comp_bijective]
    have heq : (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).toLinearMap ∘ₗ
        Finsupp.linearCombination p.ResidueField
          (TensorProduct.mk Rp p.ResidueField (Rp ⊗[R] M) 1 ∘ (TensorProduct.mk R Rp M 1 ∘ v)) =
        Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i) := by
      ext i
      simp
    convert hbij using 1
    rw [← heq, LinearMap.coe_comp]
    rfl
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective
    (Finsupp.linearCombination R v) p _ _ hloc
  refine ⟨g, hg, fun x => ?_, fun c hc => ?_⟩
  · obtain ⟨y, hy⟩ := h.2 (LocalizedModule.mk x 1)
    induction y using LocalizedModule.induction_on with
    | h c s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨⟨u, hu⟩, hu'⟩ := hy
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, hb⟩ := s.2
      refine ⟨a + b, g ^ a • c, ?_⟩
      have hb' : (s : R) = g ^ b := hb.symm
      simp only [Submonoid.smul_def, one_smul] at hu'
      rw [map_smul, hu', hb', smul_smul, pow_add]
  · have h0 : LocalizedModule.map (Submonoid.powers g) (Finsupp.linearCombination R v)
        (LocalizedModule.mk c 1) = LocalizedModule.map (Submonoid.powers g)
        (Finsupp.linearCombination R v) 0 := by
      rw [LocalizedModule.map_mk, hc, map_zero, LocalizedModule.zero_mk]
    have h1 := h.1 h0
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨⟨u, hu⟩, hu'⟩ := h1
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, by simpa [Submonoid.smul_def] using hu'⟩

end GlobalTheory.FibreBasisSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logDerivation_extension_basicOpen : ∀ (X : Scheme.{0}) (K : Type) [CommRing K] (s : X ⟶ Sp K) (I : X.IdealSheafData) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ Dl ∈ GlobalTheory.LogKS.logDer s I U, ∃ DlW ∈ GlobalTheory.LogKS.logDer s I W, ∀ r, DlW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := by
  first | exact @GlobalTheory.LogDerLoc.exists_logDer_basicOpen | exact GlobalTheory.LogDerLoc.exists_logDer_basicOpen | (intros; apply GlobalTheory.LogDerLoc.exists_logDer_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemMaximalIdealExpLeNormVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ShortVec

theorem nonneg_of_tendsto {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  by_contra h
  have h : q a < 0 := not_le.1 h
  have hfin : {x | ¬ (0 : ℝ) ≤ q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_ge_atTop 0)
  have hv : ∀ n : ℕ, q (((n : ℤ) + 1) • a) = ((n : ℝ) + 1) ^ 2 * q a := fun n => by
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ) + 1) • a) (fun m n e => ?_)
    (fun n => ?_) hfin
  · have e' := congrArg q e
    simp only [hv] at e'
    have e2 := mul_right_cancel₀ h.ne e'
    have e3 := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 e2
    exact_mod_cast add_right_cancel e3
  · simp only [Set.mem_setOf_eq, hv, not_le]
    exact mul_neg_of_pos_of_neg (by positivity) h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem val_mul_gen {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {a b : Ω}
    (ha : a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hb : b ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) :
    M.val (gPt p ≫ y) (a * b) = M.val (gPt p ≫ y) a * M.val (gPt p ≫ y) b :=
  RatModel.val_mul (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)) ha hb

theorem norm_th_eq_and_HH_eq {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (hc : y (cPt p) = z) (hR : ∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hAt : S.At M y y₀) (τ : S.Test p y₀) {x₀ : S.Gam} (hx₀ : M.Div S.th x₀ z) :
    ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ ∧ S.HH M z = τ.yy.ker := by
  have hsp := RatModel.gPt_specializes hc (IsLocalRing.closedPoint (PadicAlgCl p))
  have hy : ∀ x, y₀ ⟨S.th x, S.th_mem x⟩ = M.val (gPt p ≫ y) (S.th x) := fun x => hAt _
  have hmul : ∀ x, ‖M.val (gPt p ≫ y) (S.th x)‖ =
      ‖M.val (gPt p ≫ y) (S.th x / S.th x₀)‖ * ‖M.val (gPt p ≫ y) (S.th x₀)‖ := by
    intro x
    rw [← norm_mul, ← val_mul_gen y (RatModel.O_le_of_specializes hsp (hx₀.2 x))
      (hR _ (S.th_mem x₀)), div_mul_cancel₀ _ hx₀.1]
  have hδ : ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ := by
    apply le_antisymm
    · rw [← hy]
      exact τ.δ_max.2 ⟨x₀, rfl⟩
    · obtain ⟨x₁, hx₁⟩ := τ.δ_max.1
      simp only [hy] at hx₁
      rw [← hx₁, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hc (hx₀.2 x₁))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    change M.Div S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff hc (hx₀.2 x), hmul x, hδ]
    exact (mul_eq_right₀ τ.δ_pos.ne').symm
  refine ⟨hδ, ?_⟩
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext x
  rw [key x, Set.mem_setOf_eq, hy]

theorem exists_open (S : ThetaSys o Ω) (M : RatModel o Ω) (b : Ω) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ S.R ≤ M.ringOn U ∧ b ∈ M.ringOn U := by
  obtain ⟨s, hs⟩ := S.fg
  refine ⟨⟨{z | b ∈ M.O z} ∩ ⋂ a ∈ s, {z | a ∈ M.O z},
    (M.isOpen_setOf_mem_O b).inter (isOpen_biInter_finset fun a _ => M.isOpen_setOf_mem_O a)⟩,
    ⟨genericPoint M.Z, ?_, ?_⟩, ?_, RatModel.mem_ringOn.2 fun z hz => hz.1⟩
  · simp [RatModel.O_genericPoint]
  · simp [RatModel.O_genericPoint]
  · rw [← hs]
    exact Algebra.adjoin_le fun a ha => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 hz.2 a ha

end GlobalTheory.ShortVec

namespace GlobalTheory

open ShortVec

theorem exists_mem_maximalIdeal_exp_le_norm_val :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω),
    IsNormalScheme M.Z → M.HasDiv S.th → S.HasTests → ∀ (z₁ : M.Z), IsClosed ({z₁} : Set M.Z) →
    ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p), y (cPt p) = z₁ →
    (∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) → S.At M y y₀ →
    ∀ (τ : S.Test p y₀) (α : τ.X), (∀ v0, τ.q α ≤ τ.q (α + S.N • v0)) → 0 < τ.q α →
    ∃ h ∈ maximalIdeal (M.Z.presheaf.stalk z₁),
      Real.exp (-(τ.q α / S.N)) ≤ ‖M.val (gPt p ≫ y) (M.stalkHom z₁ h)‖ := by
  intro o Ω _ _ _ hb S M hn hd hT z hz p _ y y₀ hc hR hAt τ α hα hpos
  haveI := hb.ft
  haveI := hb.char
  obtain ⟨j, hj⟩ := hd z
  obtain ⟨hδ, hH⟩ := norm_th_eq_and_HH_eq hc hR hAt τ hj
  obtain ⟨k, hk, he⟩ := τ.eq α hα
  obtain ⟨U, hU, hRU, hbU⟩ := exists_open S M (S.FF _ (τ.wt α) k / S.th j)
  have hreg : S.FF _ (τ.wt α) k / S.th j ∈ M.O z := by
    refine ((classical_points_and_local_regularity o Ω M U fun x => ⟨hn.1 x, hn.2 x⟩).1 U le_rfl hU z hz).2 _ hbU fun p' _ y' hy' => ?_
    let w : Sp (PadicAlgCl p') := IsLocalRing.closedPoint (PadicAlgCl p')
    have hw : (gPt p' ≫ y') w ∈ (U : Set M.Z) := hy'.2 ⟨w, rfl⟩
    have hle : S.R ≤ M.O ((gPt p' ≫ y') w) := hRU.trans (RatModel.ringOn_le_O hw)
    let y₀' : S.R →+* PadicAlgCl p' :=
      (RatModel.valHom (gPt p' ≫ y') _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
    have hint : ∀ a : o, ‖y₀' (algebraMap o S.R a)‖ ≤ 1 := fun a =>
      hy'.norm_val_le_one (x := algebraMap o Ω a) ((M.O z).algebraMap_mem a)
    have hAt' : S.At M y' y₀' := fun _ => rfl
    obtain ⟨τ'⟩ := hT p' y₀' hint
    obtain ⟨hδ', hH'⟩ := norm_th_eq_and_HH_eq hy'.1 (fun a ha => hle ha) hAt' τ' hj
    obtain ⟨β, -, -, hβ⟩ := (thetaSys_norm_FF_le_exp o Ω S (test_weights o Ω S) p' y₀' τ' hint _ (τ.wt α) k hk
      τ.isoFree).2 (by rw [← hH', hH])
    have hexp : Real.exp (-(τ'.q β / S.N)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (nonneg_of_tendsto _ τ'.pos β) (Nat.cast_nonneg _)))
    have hmul := val_mul_gen y' (RatModel.ringOn_le_O hw hbU) (hle (S.th_mem j))
    rw [div_mul_cancel₀ _ hj.1] at hmul
    rw [hAt'] at hβ
    change ‖M.val (gPt p' ≫ y') (S.FF _ (τ.wt α) k)‖ ≤ _ at hβ
    rw [hmul, norm_mul, hδ', mul_comm] at hβ
    exact (le_of_mul_le_mul_left hβ τ'.δ_pos).trans hexp
  have hmul := val_mul_gen y (RatModel.O_le_of_specializes (RatModel.gPt_specializes hc _) hreg) (hR _ (S.th_mem j))
  rw [div_mul_cancel₀ _ hj.1] at hmul
  rw [hAt] at he
  change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = _ at he
  rw [hmul, norm_mul, hδ, mul_comm] at he
  have he' := mul_left_cancel₀ τ.δ_pos.ne' he
  have hN : (0 : ℝ) < S.N := by
    have := S.N_ge
    exact_mod_cast (by omega : 0 < S.N)
  have hlt : ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k / S.th j)‖ < 1 := by
    rw [he']
    exact Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hpos hN))
  have hnu := (RatModel.norm_val_lt_one_iff hc hreg).1 hlt
  refine ⟨(M.stalkEquiv z).symm ⟨_, hreg⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map]
    exact hnu
  · rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    exact he'.ge

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationExtendingMapFromOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section

theorem GlobalTheory.CompHS.exists_modif_map_of_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  intro hPr F _ _ Y T _ p d t U r₀ hs hpY hpT hU hr
  obtain ⟨N, i, hi, hit⟩ := hpT
  have hφ : (r₀ ≫ i) ≫ PSpace.str F N = U.ι ≫ p := by rw [Category.assoc, hit, hr]
  obtain ⟨w, i₀, hw₀, hwU, hext⟩ := GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace F Y p N U (r₀ ≫ i) hφ hU
  obtain ⟨I, hI0, hIU, hC⟩ := GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family Y N w i₀ U hw₀ hwU
  obtain ⟨Y', s, hY', hs', hp', -, hiso, hEC, -⟩ := hPr F d Y p inferInstance hs hpY I hI0
  have hUle : U ≤ I.support.compl := fun y hy => hIU y hy
  have hisoU : IsIso (s ∣_ U) := ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le s hUle
  have : Nonempty U := hU.to_subtype
  let c : U.toScheme ⟶ Y' := inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι
  have hc : c ≫ s = U.ι := by simp [c, morphismRestrict_ι]
  have hcη : c (genericPoint U) = genericPoint Y' := genericPoint_eq_of_isOpenImmersion c
  have hη : s (genericPoint Y') = genericPoint Y := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hne : ((s ⁻¹ᵁ U : Y'.Opens) : Set Y').Nonempty :=
    ⟨genericPoint Y', show s (genericPoint Y') ∈ U from hη ▸ GlobalTheory.Cartier.gen_mem hU.some_mem⟩
  have hdense : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y') := (s ⁻¹ᵁ U).isOpen.dense hne
  let M : Modif p U d := ⟨Y', s, hs', hp', hisoU, hdense⟩
  obtain ⟨g, hg1, hg2⟩ := hext Y' s hη (hC Y' s hη hEC)
  obtain ⟨r, hr'⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i g _ hdense fun x hx => by
    refine ⟨(s ∣_ U ≫ r₀) ⟨x, hx⟩, ?_⟩
    have e := congrArg (fun f : (s ⁻¹ᵁ U).toScheme ⟶ PSpace F N => f ⟨x, hx⟩) hg2
    exact e.symm
  refine ⟨M, r, hY', ?_, ?_⟩
  · show r ≫ t = s ≫ p
    rw [← hit, ← Category.assoc, hr', hg1]
  · show (s ⁻¹ᵁ U).ι ≫ r = (s ∣_ U) ≫ r₀
    rw [← cancel_mono i, Category.assoc, hr', hg2, Category.assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoClassifyingOfInjectiveFamilyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mono_classifying_of_injective_family : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → Inj A M → ∃ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' ∧ Same A M P (fst U S') φ ∧ Mono φ.left := by
  first | exact @GlobalTheory.DualCon.classify_mono | exact GlobalTheory.DualCon.classify_mono | (intros; apply GlobalTheory.DualCon.classify_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowMemCartierMultipleOfRegularLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem regAt_pow_of_regAt {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {u : Y.functionField} (h : RegAt y u) (n : ℕ) :
    RegAt y (u ^ n) :=
  have ⟨a, ha⟩ := h; ⟨a ^ n, by rw [map_pow, ha]⟩

theorem exists_regAt_mul_pow_affine {Y : Scheme.{0}} [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (hg : genericPoint Y ∈ U) {u g : Y.functionField} (hu0 : u ≠ 0) (hu : ∀ y ∈ U, RegAt y u)
    (h : ∀ y ∈ U, UnitAt y u → RegAt y g) : ∃ n : ℕ, ∀ y ∈ U, RegAt y (g * u ^ n) := by
  obtain ⟨f, rfl⟩ := exists_fnOf_eq hg hu
  have hb : genericPoint Y ∈ Y.basicOpen f := (unitAt_fnOf_iff hg hg f).1 (unitAt_genericPoint hu0)
  obtain ⟨b, rfl⟩ := exists_fnOf_eq hb fun y hy =>
    h y (Y.basicOpen_le f hy) ((unitAt_fnOf_iff (Y.basicOpen_le f hy) hg f).2 hy)
  have := hU.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) b
  refine ⟨n, fun y hy => ?_⟩
  have e' := congrArg (fnOf _ hb) e
  have r (c : Γ(Y, U)) : fnOf _ hb (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) c) = fnOf U hg c :=
    fnOf_resG (Y.basicOpen_le f) hb c
  simp only [map_mul, r] at e'
  rw [map_pow] at e'
  rw [e']
  exact regAt_fnOf hy hg a

theorem exists_mul_pow_mem_sec (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] (D : CartierDiv Y) (k : ℕ)
    (s : Y.functionField) (hs : s ∈ Sec D k) (g : Y.functionField) (hg : ∀ y ∈ locus D k s, RegAt y g) :
    ∃ n : ℕ, g * s ^ n ∈ Sec D (k * n) := by
  by_cases hs0 : s = 0
  · refine ⟨1, fun x => ?_⟩
    rw [hs0, pow_one, mul_zero]
    exact (CartierDiv.vanishesAt_zero _ x).regularAt
  have key (x : Y) : ∃ U : Y.Opens, x ∈ U ∧ ∃ n : ℕ, ∀ m, n ≤ m → ∀ y ∈ U,
      ((k * m) • D).RegularAt y (g * s ^ m) := by
    obtain ⟨V, hV, e, he⟩ := (k • D).exists_isEqn_nhds x
    obtain ⟨U, hU, hx, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
    have hu (y) (hy : y ∈ U) : RegAt y (s * e) := (he y (hUV hy)).regularAt_iff.1 (hs y)
    obtain ⟨n, hn⟩ := exists_regAt_mul_pow_affine (g := g) hU (gen_mem hx) (mul_ne_zero hs0 e.ne_zero) hu
      fun y hy h => hg y ⟨e, he y (hUV hy), h⟩
    refine ⟨U, hx, n, fun m hm y hy => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [mul_nsmul]
    refine ⟨_, (he y (hUV hy)).nsmul _, ?_⟩
    have := (hn y hy).mul (regAt_pow_of_regAt (hu y hy) d)
    rwa [_root_.mul_assoc, ← pow_add, mul_pow, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val] at this
  choose U hU n hn using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set Y)) (fun x => (U x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩
  refine ⟨t.sup n, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact hn x _ (Finset.le_sup hx) y hy

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  first | exact @GlobalTheory.DetLine.exists_unif_of_frame | exact GlobalTheory.DetLine.exists_unif_of_frame | (intros; apply GlobalTheory.DetLine.exists_unif_of_frame <;> assumption)
end

