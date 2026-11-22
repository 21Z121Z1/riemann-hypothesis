import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0292
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegersStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_bound_integers : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K), Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | exact GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrixStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_block_matrix : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  first | exact @GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes | exact GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes | (intros; apply GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrderStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strict_block_order : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  first | exact @GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | exact GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | (intros; apply GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBaseStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_chern_class_nilpotent_base : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  first | exact @GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | exact GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | (intros; apply GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquivStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_transport_equiv : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  first | exact @GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration | exact GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration | (intros; apply GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSizeStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_of_size : MulF → MulI → SzFin → FinSupp := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | exact GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | (intros; apply GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotientStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_thickening_quotient : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))), FlatT T → FlatT (qT hn T) := by
  first | exact @GlobalTheory.CompanionTheory.FlatThick.flatT_qT | exact GlobalTheory.CompanionTheory.FlatThick.flatT_qT | (intros; apply GlobalTheory.CompanionTheory.FlatThick.flatT_qT <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameRight
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GlobalTheory.CompanionTheory.DegMoveProof

namespace GlobalTheory.CompanionTheory.DegRightProof

theorem frame_right {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ} (x h : GA E n)
    (M : Matrix (Fin n) (Fin k) (Ad E)) :
    h.val * (((x * h)⁻¹ : GA E n).val * M) = (x⁻¹ : GA E n).val * M := by
  rw [← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left]

theorem degRight_of : MulF → MulI → SzFin → FinSupp → DegRight := by
  intro hF hI hSz hFS E _ _ _ n
  have hb : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), by positivity,
    fun x h W => ?_⟩
  obtain ⟨hLI, -⟩ := lin_basisMat W
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have hY : (N.map (algebraMap E (Ad E)) * (x * h : GA E n).val) *
      (((x * h)⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (x * h : GA E n).val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn h _ _ hY
  rw [frame_right] at hc
  have e1 : deg (x * h) W = degG (x * h) (basisMat W) := rfl
  have e2 : deg x W = degG x (basisMat W) := rfl
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg h.val
  have hS' := logSizeM_nonneg (h⁻¹ : GA E n).val
  have hsz : logSize h = logSizeM h.val + logSizeM (h⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM h.val = S at *
  generalize logSizeM (h⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hpos : 0 ≤ (n : ℝ) * (S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegRightProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSupStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_add_le_sup : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)), genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem mem_twSecs_of_mem_twPow {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (n : ℤ) (m : ℕ) : twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  letI : Algebra A Γ(X, ⊤) := GroundTheory.Arith.SchemeCoh.overAlgebra (CommRingCat.of A)
  have fac : ∀ a ∈ I ^ m, ∃ ψ : P ⟶ GroundTheory.Arith.SchemeCoh.idealPow I P m,
      ψ ≫ GroundTheory.Arith.SchemeCoh.idealPowι I P m = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    intro a ha
    rw [← GroundTheory.Arith.SchemeCoh.span_idealGen (I ^ m)] at ha
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
    let u : P ⟶ ⨁ fun _ : Fin (GroundTheory.Arith.SchemeCoh.idealGenNum (I ^ m)) => P :=
      biproduct.lift fun k => GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c k))
    have hu : u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m) = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      rw [← hc]
      simp only [u, GroundTheory.Arith.SchemeCoh.idealSumMap, biproduct.lift_desc, GroundTheory.Arith.SchemeCoh.smulHom_comp_smulHom, map_sum, GroundTheory.Arith.SchemeCoh.smulHom_sum,
        smul_eq_mul, map_mul]
    refine ⟨kernel.lift (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))) (u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))
      (by rw [Category.assoc, cokernel.condition, comp_zero]), ?_⟩
    rw [← hu]
    exact kernel.lift_ι _ _ _
  have act : ∀ (r : Γ(X, ⊤)) (s : Γ(GlobalTheory.twistZ P H n, ⊤)),
      ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (GroundTheory.Arith.SchemeCoh.smulHom P r)) ⊤) s
        = GroundTheory.Arith.SchemeCoh.restrictTop ⊤ r • s := by
    intro r s
    rw [GlobalTheory.Twist.sec_ext_iff]
    intro i
    rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]
    congr 1
    exact (GroundTheory.Arith.SchemeCoh.restrictTop_restrict _ r).symm
  have base : ∀ a ∈ I ^ m, ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤ a • s ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)) := by
    intro a ha s
    obtain ⟨ψ, hψ⟩ := fac a ha
    have e : (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (powSub I P m).arrow
        = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      show (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (Subobject.mk (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).arrow = _
      rw [Category.assoc, Subobject.underlyingIso_arrow, hψ]
    refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n)
      (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv)) ⊤) s, ?_⟩
    have h2 := act (algebraMap A Γ(X, ⊤) a) s
    rw [← e] at h2
    erw [GlobalTheory.Twist.map_comp, Scheme.Modules.Hom.comp_app] at h2
    try erw [ConcreteCategory.comp_apply] at h2
    exact h2
  let K : Ideal Γ(X, ⊤) :=
    { carrier := {r | ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), r • s ∈ Set.range
        (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤))}
      add_mem' := by
        intro x y hx hy s
        obtain ⟨u, hu⟩ := hx s
        obtain ⟨v, hv⟩ := hy s
        exact ⟨u + v, by rw [map_add, hu, hv, add_smul]⟩
      zero_mem' := by
        intro s
        exact ⟨0, by rw [map_zero, zero_smul]⟩
      smul_mem' := by
        intro t x hx s
        obtain ⟨u, hu⟩ := hx (t • s)
        exact ⟨u, by rw [hu, smul_eq_mul, mul_comm, mul_smul]⟩ }
  have hJ : Ideal.map (GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤) (I ^ m) ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact base a ha
  intro c hc
  simp only [twPow, SetLike.mem_coe] at hc
  refine Submodule.smul_induction_on (p := fun x => x ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)))
    hc ?_ ?_
  · intro r hr s _
    exact hJ hr s
  · intro x y hx hy
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]⟩

theorem genSub_le_powSub : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (m : ℕ) (c : Γ(GlobalTheory.twistZ P H n, ⊤)),
    c ∈ twPow I H n P m → genSub hH n c ≤ powSub I P m := by
  intro A _ _ I X _ H hH P _ n m c hc
  exact genSub_le hH (powSub I P m) n c (mem_twSecs_of_mem_twPow I H P n m hc)

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules} (S : Subobject P) (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), b ∈ twSecs H n S → genSub hH n b ≤ S := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_quasicoherent : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), (genSub hH n b : X.Modules).IsQuasicoherent := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub | exact GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub <;> assumption)
end

