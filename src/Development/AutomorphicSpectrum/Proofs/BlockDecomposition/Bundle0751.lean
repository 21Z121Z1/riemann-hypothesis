import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionsEmbedCuspidalDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0730
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0719
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToQuotEqZeroIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0585
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0743
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleRev

theorem exists_isSocle_prodIrr_of_isRevOrdered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k →
    LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N),
    IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  intro k _ _ _ _ hA hJ hI hC h N Γ y hd hR hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order Γ
  have hR' : IsRevOrdered (Γ ∘ σ) := GlobalTheory.T.canonical_segments_reverse_ordered _ hσ
  have hd' : ∑ a, (y (σ a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp σ (fun a => (y a).1)
  obtain ⟨e₁⟩ := GlobalTheory.T.reverse_ordered_product_perm_equiv hA hC Γ σ y hd hd' hR hR' hL
  have hL' : ∀ i, IsLSeg ((Γ ∘ σ) i) ((y ∘ σ) i).rep := fun i => hL (σ i)
  obtain ⟨g, z, hz, ⟨e₂⟩, hjm⟩ := GlobalTheory.T.canonical_product_equiv_multiplicity_one hA hJ hI (Γ ∘ σ) (y ∘ σ) hd' hσ hL'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.socle_of_multiplicity_one hA z hz hjm
  exact ⟨τ, hτ.of_equiv (Representation.Equiv.refl _) (e₁.trans e₂).symm⟩

end GlobalTheory.CompanionTheory.SocleRev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOne
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_one_of_eqv (n : ℕ) (lev : Fin n → ℕ) (f h : SmF n) (_hf : f ∈ Eqv lev f.1) (_hf1 : f.1 1 = 1)
    (hh : h ∈ Eqv lev f.1) (X : Mat n) (hX : ∀ a b, lev a < lev b → X a b = 0) :
    (DR X h).1 1 = (DR X f).1 1 * h.1 1 := by
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have dh := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 h1).hasFDerivAt
  have df := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth f.2.1 h1).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    simp only [one_smul] at this
    exact this
  have hc0 : (1 : Mat n) = (fun t : ℝ => (1 : Mat n) + t • X) 0 := by simp
  have Dh := dh.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0
  have Df := (df.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).mul_const (h.1 1)
  have hev : ∀ᶠ t : ℝ in nhds 0, (1 : Mat n) + t • X ∈ GLs n :=
    hc.continuousAt.eventually_mem (by
      have hm : (1 : Mat n) + (0 : ℝ) • X = 1 := by simp
      rw [hm]
      exact GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds h1)
  have heq : (h.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) =ᶠ[nhds 0]
      fun t => (f.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) t * h.1 1 := by
    filter_upwards [hev] with t ht
    have hp : (1 : Mat n) + t • X ∈ Pb lev := by
      refine ⟨ht, fun a b hab => ?_⟩
      have hne : a ≠ b := fun e => (e ▸ hab : lev a < lev a).false
      simp [hX a b hab, Matrix.one_apply_ne hne]
    have := hh _ hp 1 h1
    simpa using this
  have key := (Dh.congr_of_eventuallyEq heq.symm).unique Df
  rw [DR_apply _ _ h1, DR_apply _ _ h1]
  show fderiv ℝ h.1 1 (1 * X) = fderiv ℝ f.1 1 (1 * X) * h.1 1
  rw [one_mul]
  exact key

end GlobalTheory.CompanionTheory.ModelS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativePreservesEquivariant
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_mem_Eqv (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) :
    h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  intro hh p hp g hg
  have hpg : p * g ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hp.1 hg
  rw [DR_apply X h hpg, DR_apply X h hg]
  have dg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hg
  have dpg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hpg
  have ev : (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) =ᶠ[nhds g] fun y => φ p • h.1 y := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact hh p hp y hy
  have e1' : fderiv ℝ (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) g (g * X)
      = fderiv ℝ h.1 (p * g) (p * (g * X)) :=
    GlobalTheory.CompanionTheory.RCalc.fderiv_comp_clm (GlobalTheory.CompanionTheory.RCalc.mulL p) dpg (g * X)
  rw [ev.fderiv_eq] at e1'
  have e2' := GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply dg (φ p) (g * X)
  simp only [Rd]
  rw [Matrix.mul_assoc, ← e1']
  exact e2'

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHom
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LieAct

variable {n : ℕ}

theorem SmF_ext {a b : SmF n} (h : ∀ g ∈ GLs n, a.1 g = b.1 g) : a = b := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact h g hg
  · rw [a.2.2 g hg, b.2.2 g hg]

theorem Rd_DR (X Y : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (DR Y h).1 g = Rd X (Rd Y h.1) g := by
  have hev : (DR Y h).1 =ᶠ[nhds g] Rd Y h.1 := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact DR_apply Y h hy
  simp only [Rd]
  rw [hev.fderiv_eq]

theorem DR_add (X Y : Mat n) : DR (X + Y) = DR X + DR Y := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, DR_apply _ _ hg, Rd, Matrix.mul_add, map_add]

theorem DR_smul (r : ℝ) (X : Mat n) : DR ((r : ℂ) • X) = (r : ℂ) • DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  have e : g * ((r : ℂ) • X) = r • (g * X) := by
    ext a b
    simp [Matrix.mul_apply, Finset.mul_sum, Complex.real_smul, mul_left_comm]
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, DR_apply _ _ hg, Rd, e, map_smul,
    Complex.real_smul, smul_eq_mul]

theorem DR_bracket (X Y : Mat n) : DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, DR_apply _ _ hg, Rd_DR _ _ _ hg]
  exact (GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y h.2.1 hg).symm

theorem DR_lie (n : ℕ) : (∀ X Y : Mat n, DR (X + Y) = DR X + DR Y) ∧
    (∀ (r : ℝ) (X : Mat n), DR ((r : ℂ) • X) = (r : ℂ) • DR X) ∧
    (∀ X Y : Mat n, DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X) :=
  ⟨DR_add, DR_smul, DR_bracket⟩

end GlobalTheory.CompanionTheory.ModelS.LieAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionsEmbedCuspidalDerivativeStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (a b : GRep k (m + 1))
    (hs : IsSmooth a.ρ) (hb : IsSmooth b.ρ) (hi : a.ρ.IsIrreducible) (hcu : IsCuspidal a.ρ),
    ∃ ι : SchF k (m + 1) b.V →ₗ[ℂ] (Rm ψ a b).V, Function.Injective ι ∧
      (∀ x f, ι (shiftF x f) = (Rm ψ a b).ρ (uM (m + 1) x) (ι f)) ∧
      (∀ g f, ι (actF (b.tw (-1 / 2)).ρ g f) = (Rm ψ a b).ρ (levi k (m + 1) g) (ι f)) ∧
      ∀ x v, (Rm ψ a b).ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι := by
  first | exact @GlobalTheory.CompanionTheory.BZShellOpen.open_part | exact GlobalTheory.CompanionTheory.BZShellOpen.open_part | (intros; apply GlobalTheory.CompanionTheory.BZShellOpen.open_part <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoIrreducibleSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bot_ne_top_of_isSubquotient {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {V Y : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] {P : Representation ℂ (GL (Fin N) k) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hτ : τ.IsIrreducible)
    (h : IsSubquotient τ (jac e P)) : (⊥ : Subrepresentation P) ≠ ⊤ := by
  intro hb
  obtain ⟨T, f, hf⟩ := h
  haveI := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  obtain ⟨t, rfl⟩ := hf w
  have hV : ∀ v : V, v = 0 := fun v => by
    have h1 : v ∈ (⊤ : Subrepresentation P).toSubmodule := trivial
    rw [← hb] at h1
    exact h1
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ t.1
  have h0 : t = 0 := Subtype.ext (by rw [← hu, hV u]; rfl)
  exact hw (by rw [h0, map_zero])

abbrev clx {n : ℕ} (c : Fin 2 → IrrCl (GL (Fin n) k)) : Fin 2 → IrrGL k := fun a => ⟨n, c a⟩

theorem jm_perm (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n N : ℕ} (c : Fin 2 → IrrCl (GL (Fin n) k))
    (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c)) (σ : Equiv.Perm (Fin 2))
    (hy : ∑ a, (clx c (σ a)).1 = N) (hd : ∑ a, (clx c a).1 = N) :
    jm (fun a => clx c (σ a)) hy (prodIrr (clx c) hd) = 1 := by
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (clx c) _ hd hy hc fun a => hc _]
  have : {e : Fin 2 ≃ Fin 2 | ∀ a, clx c (σ a) = clx c (e a)} = {σ} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => (Equiv.ext fun a => hinj (h a)).symm
    · rintro rfl a
      rfl
  rw [this, Set.ncard_singleton]
  simp

theorem exists_surjective_jac {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : ρ.IsIrreducible)
    (S : Subrepresentation (parInd e ρ)) (hS : S.toRepresentation.IsIrreducible) :
    ∃ q : (jac e S.toRepresentation).IntertwiningMap ρ, Function.Surjective q := by
  haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hS
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  have h1 := GlobalTheory.CompanionTheory.FrobJm.frobMap_ne_zero e (incl S)
    ⟨v, fun h => hv (incl_injective S (h.trans (map_zero (incl S)).symm))⟩
  exact ⟨_, GlobalTheory.CompanionTheory.FrobJm.surjective_of_ne_zero hρ _ h1⟩

set_option maxHeartbeats 1000000 in

theorem two_cusp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n N : ℕ} (hn : 0 < n)
    (c : Fin 2 → IrrCl (GL (Fin n) k)) (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c))
    (hd : ∑ a, (clx c a).1 = N) (hred : ¬ (prodIrr (clx c) hd).IsIrreducible) :
    ∃ S : Subrepresentation (prodIrr (clx c) hd), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (prodIrr (clx c) hd), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (stdBlocks (fun a => (clx c a).1) hd) S.toRepresentation).Equiv
        (piTensor fun a => (clx c a).rep)) := by
  have hy : ∑ a, (clx c ((Fin.revPerm : Equiv.Perm (Fin 2)) a)).1 = N := hd
  have hP : IsSmooth (prodIrr (clx c) hd) := isSmooth_prodIrr _ hd
  have h₀ := GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (clx c)
  have h₁ := GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA fun a => clx c ((Fin.revPerm : Equiv.Perm (Fin 2)) a)
  have m₀ : jm (clx c) hd (prodIrr (clx c) hd) = 1 := jm_perm hA c hc hinj 1 hd hd
  have m₁ := jm_perm hA c hc hinj Fin.revPerm hy hd
  refine exists_unique_sub (stdBlocks (fun a => (clx c a).1) hd) hP
    (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA _ hd)
    (bot_ne_top_of_isSubquotient _ h₀ (jhMult_ne_zero_iff.1 (ne_of_eq_of_ne m₀ one_ne_zero))) hred h₀ h₁
    m₀.le m₁.le ?_ ?_ ?_ ?_
  · intro Y _ _ τ hτ hs
    exact cell_cases (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1 (n := n) hn
      (X := fun a => (c a).rep.V) (fun a => (c a).rep.ρ)
      (fun a => (c a).rep.smooth) (fun a => (hc a).2) _ h₀ h₁ hτ hs
  · exact fun S hS => exists_surjective_jac (stdBlocks (fun a => (clx c a).1) hd) h₀ S hS
  · intro U _ _ Q hs hi hsub
    obtain ⟨e', he, h1⟩ := GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA _ hd hc Q hs hi hsub
    rcases GlobalTheory.CompanionTheory.SegFine2.perm_two e' with rfl | rfl
    · exact Or.inl (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1))
    · exact Or.inr (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1))
  · intro S hS
    exact (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ _ _ _
      ((IsSubquotient.of_injective (incl S) (incl_injective S)).isSmooth hP) (hasFiniteLength_of_isIrreducible hS)

theorem concl_of_classes (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {d : ℕ} (hd0 : 0 < d)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Fin 2 → Representation ℂ (GL (Fin d) k) V)
    (c : Fin 2 → IrrCl (GL (Fin d) k)) (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c))
    (hd : ∑ a, (clx c a).1 = 2 * d) (E : ∀ a, (τ a).Equiv (c a).rep.ρ)
    (H : ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ).IsIrreducible) :
    ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor τ)) := by
  have he : GlobalTheory.Published.consecBlocks 2 d = stdBlocks (fun a => (clx c a).1) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun a => (clx c a).1) hd a j).symm)
    simp [mul_comm, add_comm]
  rw [he] at H ⊢
  let Φ : (multiProd (stdBlocks (fun a => (clx c a).1) hd) τ).Equiv (prodIrr (clx c) hd) := multiProdEquiv _ E
  exact GlobalTheory.CompanionTheory.SegFine2.exists_sub_of_equiv (stdBlocks (fun a => (clx c a).1) hd) Φ.symm (piTensorEquiv E).symm
    (two_cusp hA hd0 c hc hinj hd fun h => H (GlobalTheory.Parabolic.isIrreducible_of_equiv Φ.symm h))

theorem segment_two : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible) →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2))) := by
  intro H k _ _ _ _ d hd0 σ hc
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  let Δ : Segment k := ⟨d, hd0, σ.cl, ⟨σ, rfl, hc⟩, 2, two_pos⟩
  let c : Fin 2 → IrrCl (GL (Fin d) k) := fun a => (Δ.term a).2
  have hd : ∑ a, (clx c a).1 = 2 * d := Δ.sum_term_fst
  exact concl_of_classes hA hd0 (segTerm σ.ρ 2) c (fun a => Δ.isCusp_term a)
    (GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ) hd
    (fun a => (twistEquiv (equivRep σ) _).trans (Δ.first.twEquiv _ (isSmoothChar_absPow _)))
    (H k d hd0 σ hc)

end GlobalTheory.CompanionTheory.SegTwo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRange
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx db hdb Φ hΦ
  obtain ⟨μ₁, μ₂, c, h1, h2, s1, s2, hc, hme, hmap⟩ := GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n dx hdx.1
  obtain ⟨ν₁, ν₂, c', g1, g2, t1, t2, hc', hme', hmap'⟩ := GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n db hdb.1
  obtain ⟨k, P, Q, hP, hQ, hsum⟩ := id hΦ
  have hpureSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat
      (fun X : Fin n → Fin M → AF F ⊗[F] E => P i (projInf X) * Q i (projFin X)) := fun i =>
    GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod (hP i) (hQ i) fun _ => rfl
  have hfac : ∀ i (b : HermR (AF F) σ n), starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
      (c.toReal : ℂ) * (starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) (hermInf σ b) *
        starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) (hermFin σ b)) := by
    intro i b
    let A : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun x =>
      P i x * psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
          gramR (Ainf F) σ J x)))
    let B : (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun y =>
      Q i y * psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
          gramR (Af F) σ J y)))
    let G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun z => A z.1 * B z.2
    have e1 : starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
        ∫ X, G (projInf X, projFin X) ∂dx := by
      unfold starN
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      show _ * _ = G _
      rw [GlobalTheory.T.character_trace_pairing_eq_inner_psi F E σ hCM M J n ψ b X]
      simp only [G, A, B]
      ring
    have e2 := hme.integral_map (μ := dx) G
    have e3 : ∫ z, G z ∂μ₁.prod μ₂ = (∫ x, A x ∂μ₁) * ∫ y, B y ∂μ₂ := integral_prod_mul A B
    rw [e1]
    refine e2.symm.trans ?_
    rw [hmap, integral_smul_measure, e3, Complex.real_smul]
    rfl
  have hpure : ∀ i, Integrable (starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X))) db := by
    intro i
    have hA := GlobalTheory.T.archimedean_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₁ h1 ν₁ g1 (P i) (hP i)
    have hB := GlobalTheory.T.finite_adelic_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₂ h2 ν₂ g2 (Q i) (hQ i)
    have hAB := hA.mul_prod hB
    have hAB' : Integrable (fun z : HermR (Ainf F) σ n × HermR (Af F) σ n =>
        starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) z.1 * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) z.2)
        (db.map (fun b => (hermInf σ b, hermFin σ b))) := by
      rw [hmap']
      exact hAB.smul_measure hc'
    have := (hme'.integrable_map_iff.1 hAB').const_mul (c.toReal : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    exact (hfac i b).symm
  have hdec : starN σ J ψ dx Φ = fun b => ∑ i, starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b := by
    funext b
    unfold starN
    rw [← integral_finset_sum _ fun i _ => GlobalTheory.T.twisted_schwartz_function_integrable F E σ hCM M J n ψ hψ dx hdx.1 _ (hpureSB i) b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Φ X * _ = _
    rw [hsum, Finset.sum_mul]
  rw [hdec]
  exact integrable_finset_sum _ fun i _ => hpure i

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupportAltBis
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_and_hasCompactSupport_testT : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) → Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧ HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureLocallyFiniteInvariantStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_locally_finite_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesSiegelBoundStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_siegel_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ∀ (C₁ : Set (GA D V)), IsCompact C₁ → ∀ N : ℕ, ∃ (C : ℝ) (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n, ‖f (fun τ i j => compAt θ τ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j) * g (fun i j => finPart D ((HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j))‖ₑ ≤ ENNReal.ofReal C * ∏ j : Fin n, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant | exact GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant | (intros; apply GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

def whitT (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank n)) (lam : Measure (hermA D n))
    (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (φ : Mx D V.rank n → ℂ) (T : Mx D n n) (g : G D n) :
    ℂ → ℂ :=
  fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ φ b *
    ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) ∂lam

def WhitKA : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
  ∀ a : GL (Fin n) (AE D), ∀ k ∈ K D n,
    HolValueAt (whitT ψ V μ lam nb w H (ω k Φ).1 (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n)
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
        IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β)

end GlobalTheory.CompanionTheory.IwaAd
end
end

