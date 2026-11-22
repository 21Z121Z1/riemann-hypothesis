import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.ProdLength

section General
variable {F G U V X : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V]
  [Module F V] [AddCommGroup X] [Module F X]

def comapSub {α : Representation F G U} {β : Representation F G V} (ι : α.IntertwiningMap β)
    (S : Subrepresentation β) : Subrepresentation α :=
  ⟨S.toSubmodule.comap ι.toLinearMap, fun g v hv => by
    show ι (α g v) ∈ S.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩

def mapSub {β : Representation F G V} {γ : Representation F G X} (p : β.IntertwiningMap γ)
    (S : Subrepresentation β) : Subrepresentation γ :=
  ⟨S.toSubmodule.map p.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨β g v, S.apply_mem_toSubmodule g hv, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ p g v⟩

theorem hasFiniteLength_of_exact {α : Representation F G U} {β : Representation F G V}
    {γ : Representation F G X} (ι : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) (hα : HasFiniteLength α) (hγ : HasFiniteLength γ) :
    HasFiniteLength β := by
  obtain ⟨hα1, hα2⟩ := (hasFiniteLength_iff_wellFounded α).1 hα
  obtain ⟨hγ1, hγ2⟩ := (hasFiniteLength_iff_wellFounded γ).1 hγ
  let f : Subrepresentation β → Subrepresentation α × Subrepresentation γ :=
    fun S => (comapSub ι S, mapSub p S)
  have hmono : Monotone f := fun S T h =>
    ⟨fun v hv => h hv, Submodule.map_mono (f := p.toLinearMap) h⟩
  have hf : StrictMono f := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h1 : (comapSub ι S).toSubmodule = (comapSub ι T).toSubmodule := congrArg (fun x => x.1.toSubmodule) heq
    have h2 : (mapSub p S).toSubmodule = (mapSub p T).toSubmodule := congrArg (fun x => x.2.toSubmodule) heq
    intro x hx
    have hpx : p x ∈ (mapSub p T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h2] at hpx
    obtain ⟨y, hy, hyx⟩ := hpx
    have hyx' : p y = p x := hyx
    obtain ⟨u, hu⟩ := hex (x - y) (by rw [map_sub, hyx', sub_self])
    have huT : u ∈ (comapSub ι T).toSubmodule := by
      show ι u ∈ T.toSubmodule
      rw [hu]
      exact T.toSubmodule.sub_mem hx (hST.le hy)
    rw [← h1] at huT
    have huS : ι u ∈ S.toSubmodule := huT
    rw [hu] at huS
    have := S.toSubmodule.add_mem huS hy
    rwa [sub_add_cancel] at this
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_injective {α : Representation F G U} {β : Representation F G V}
    (ι : α.IntertwiningMap β) (hι : Function.Injective ι) (hβ : HasFiniteLength β) :
    HasFiniteLength α := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded β).1 hβ
  have hmono : Monotone (mapSub ι) := fun S T h => Submodule.map_mono (f := ι.toLinearMap) h
  have hf : StrictMono (mapSub ι) := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h3 : (mapSub ι S).toSubmodule = (mapSub ι T).toSubmodule := congrArg (·.toSubmodule) heq
    intro x hx
    have hx' : ι x ∈ (mapSub ι T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h3] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← hι hyx]
  exact (hasFiniteLength_iff_wellFounded α).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (β : Representation F G V) :
    HasFiniteLength β := by
  haveI : Subsingleton (Subrepresentation β) := ⟨fun S T => by
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => T.toSubmodule.zero_mem, fun _ => S.toSubmodule.zero_mem⟩⟩
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩

end General

section Tensor
open GlobalTheory.ParIndExact
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasFiniteLength_extTensor_left (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hA : HasFiniteLength A)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y), σ.IsIrreducible →
      IsSubquotient σ A → HasFiniteLength (extTensor σ B)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded A).1 hA
  have key : ∀ S T : Subrepresentation A, T ≤ S → HasFiniteLength (extTensor (subQuot S T) B) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_left (F := ℂ)
        (V := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule) (W := W)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := A) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_left B ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot A
  obtain ⟨ι', hι'⟩ := extTensor_injective_left B ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

theorem hasFiniteLength_extTensor_right (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hB : HasFiniteLength B)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H Y), τ.IsIrreducible →
      IsSubquotient τ B → HasFiniteLength (extTensor A τ)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded B).1 hB
  have key : ∀ S T : Subrepresentation B, T ≤ S → HasFiniteLength (extTensor A (subQuot S T)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_right (F := ℂ) (V := V)
        (W := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := B) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_right A ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot B
  obtain ⟨ι', hι'⟩ := extTensor_injective_right A ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

end Tensor
end GlobalTheory.ProdLength

theorem GlobalTheory.ProdLength.prod₂_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  intro hBZ k _ _ _ _ r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have schur : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ (GL (Fin n) k) Y),
      IsSmooth σ → σ.IsIrreducible → ∀ φ : Y →ₗ[ℂ] Y, (∀ g x, φ (σ g x) = σ g (φ x)) →
        ∃ c : ℂ, φ = c • LinearMap.id := fun n Y _ _ σ hs hi =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO Y σ hi
      (hAdm (Fin n) Y σ hs hi)
  have hT : HasFiniteLength (extTensor π₁ π₂) :=
    GlobalTheory.ProdLength.hasFiniteLength_extTensor_left π₁ π₂ h₁ fun Y _ _ σ hσ hsq =>
      GlobalTheory.ProdLength.hasFiniteLength_extTensor_right σ π₂ h₂ fun Z _ _ τ hτ hsq' =>
        hasFiniteLength_of_isIrreducible (GlobalTheory.JacFactor.isIrreducible_extTensor σ τ hσ hτ
          (schur r Y σ (hsq.isSmooth s₁) hσ) (schur t Z τ (hsq'.isSmooth s₂) hτ))
  have hc : Continuous (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom :=
    (continuous_apply false).prodMk (continuous_apply true)
  exact hInd Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    (isSmooth_comp (isSmooth_extTensor s₁ s₂) _ hc)
    ((hasFiniteLength_comp_iff _ _ (leviTwo k (Fin r) (Fin t)).symm.surjective).2 hT)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCore
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixQuasi

variable {D : D7}

theorem pair_add_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x + x') a) = trHalf D (pairS T x a) + trHalf D (pairS T x' a) := by
  rw [← map_add]
  congr 1
  simp only [pairS, Matrix.mul_add, trace_add]

theorem pair_add_right (T : HSp D) {ρ : ℕ} (x a a' : Mx D T.rank ρ) :
    trHalf D (pairS T x (a + a')) = trHalf D (pairS T x a) + trHalf D (pairS T x a') := by
  rw [← map_add]
  congr 1
  simp only [pairS, adj_add, Matrix.add_mul, trace_add]

theorem pair_sub_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x - x') a) = trHalf D (pairS T x a) - trHalf D (pairS T x' a) := by
  rw [eq_sub_iff_add_eq, ← pair_add_left, sub_add_cancel]

theorem pair_rat {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) {x a : Mx D T.rank ρ}
    (hx : x ∈ ratMx D T.rank ρ) (ha : a ∈ ratMx D T.rank ρ) :
    ∃ c, trHalf D (pairS T x a) = algebraMap D.host.F (AF D.host.F) c := by
  rw [← d.symplOH_extX_extY]
  exact (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ (ratMx_mul hx (rat_mem _)) _ (ratMx_mul ha (rat_mem _))

theorem symplOH_coords {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (h0 : S₀.rank = 0) (u w : WO S T) :
    symplOH S T u w = trHalf D (pairS T (u ⬝ d.jX) (w ⬝ d.jY)) - trHalf D (pairS T (w ⬝ d.jX) (u ⬝ d.jY)) := by
  have hz : ∀ v : WO S₀ T, v = 0 := fun v => by
    funext i j
    exact absurd j.2 (by omega)
  have e : ∀ v : WO S T, v = d.extX T (v ⬝ d.jX) + d.extY T (v ⬝ d.jY) := fun v => by
    have h := eq_coords d v
    rwa [hz (v ⬝ d.j0), map_zero, add_zero] at h
  conv_lhs => rw [e u, e w]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    d.symplOH_extX_extX, d.symplOH_extY_extY, d.symplOH_extX_extY, symplOH_Y_X]
  ring

theorem poinX_quasi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), poinX ψ d T β (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * poinX ψ d T β w := by
  intro D ψ hψ S S₀ T ρ d h0 β γ w
  obtain ⟨δ, hδ⟩ : (ratW T S γ : WO S T) ⬝ d.jX ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have hδ' : (ratW T S γ : WO S T) ⬝ d.jX = rat δ := hδ.symm
  have ha : (ratW T S γ : WO S T) ⬝ d.jY ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have eX : (ratW T S γ + w : WO S T) ⬝ d.jX = rat δ + w ⬝ d.jX := by
    rw [← hδ']; exact Matrix.add_mul _ _ _
  have eY : (ratW T S γ + w : WO S T) ⬝ d.jY = (ratW T S γ : WO S T) ⬝ d.jY + w ⬝ d.jY := Matrix.add_mul _ _ _
  rw [symplOH_coords T d h0, hδ']
  unfold poinX
  rw [eX, eY, ← (Equiv.subRight δ).tsum_eq, ← tsum_mul_left]
  generalize (ratW T S γ : WO S T) ⬝ d.jY = a at ha ⊢
  generalize w ⬝ d.jX = x
  generalize w ⬝ d.jY = y
  congr 1
  funext g
  simp only [Equiv.subRight_apply]
  rw [rat_sub]
  have e1 : rat δ + x + (rat g - rat δ) = x + rat g := by abel
  have e2 : rat δ + x + 2 • (rat g - rat δ) = x + 2 • rat g - rat δ := by
    rw [two_smul, two_smul]; abel
  have e3 : x + 2 • rat g - rat δ = x + (rat g + rat g - rat δ) := by
    rw [two_smul]; abel
  obtain ⟨c, hc⟩ := pair_rat T d (((ratMx D T.rank ρ).sub_mem ((ratMx D T.rank ρ).add_mem (rat_mem g) (rat_mem g))
    (rat_mem δ))) ha
  have e4 : trHalf D (pairS T (x + 2 • rat g - rat δ) (a + y)) =
      algebraMap D.host.F (AF D.host.F) c + (-(trHalf D (pairS T (rat δ) y) - trHalf D (pairS T x a)) +
        trHalf D (pairS T (x + 2 • rat g) y)) := by
    rw [pair_add_right, pair_sub_left T _ _ y, e3, pair_add_left T x _ a, hc]
    ring
  rw [e1, e2, e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.1.2.2.1 c]
  ring

end GlobalTheory.BumpMixQuasi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairingStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_fock_space_stable_mul_trace_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ (q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
          ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by
  first | exact @GlobalTheory.PolMul.pol_mul_pairInf_pair | exact GlobalTheory.PolMul.pol_mul_pairInf_pair | (intros; apply GlobalTheory.PolMul.pol_mul_pairInf_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudoCoefficientUnitaryPq
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.Published

theorem pseudoCoefficientUpq_of_hypotheses (hUA : IrreducibleUnitaryAdmissible) (hKA : KFiniteCoefficientsAnalytic)
    (hCR : CharacterRegularityFiniteLength) (hPE : PseudoCoefficientExistence) (hCO : CuspidalOrbitalIntegrals) :
    PseudoCoefficientUpq := by
  intro n ε X _ _ σ h μ _
  haveI := h.1
  obtain ⟨f, hf, hbi, hpt⟩ := hPE n ε X σ h μ
  have hadm : IsAdmRep ε σ := (GlobalTheory.T.admissible_unitary_K_finite.1 hUA) n ε X σ h.2.2.1 h.2.2.2.1
  have hfl : HasFiniteLength ε σ := (GlobalTheory.T.irreducible_admissible_finite_length hKA n ε X σ ⟨h.2.1, hadm, h.2.2.2.1⟩).2
  obtain ⟨Θ, hΘ⟩ := hCR n ε μ X σ hadm hfl
  have hch : IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ := hΘ.1
  refine ⟨f, hbi, ⟨hf, hpt.1, ?_, ?_, ⟨Θ, hch, ?_⟩⟩⟩
  · intro U _ _ _ π hu hi ht hne
    exact hpt.2 U π hu hi (GlobalTheory.T.tempered_K_finite_coefficients hUA n ε μ U π hu hi ht) hne
  · intro s hs hnc dt _ _
    exact (hCO n ε X σ h μ f hf hbi hpt Θ hch s hs dt).2 hnc
  · intro s hs hc dt _ _
    exact (hCO n ε X σ h μ f hf hbi hpt Θ hch s hs dt).1 hc

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientSeparationOfHarishChandraStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudocoefficient_separation_of_harish_chandra : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation := by
  first | exact @GlobalTheory.SepPseudo.pseudoCoeffSeparation | exact GlobalTheory.SepPseudo.pseudoCoeffSeparation | (intros; apply GlobalTheory.SepPseudo.pseudoCoeffSeparation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0Statement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_schwartzBruhat_adicCompletion_pi_le_aleph0 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | exact GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | (intros; apply GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegrals
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrClassTerm

theorem integrable_descend_of_stdDom {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} {φ : G → ℂ} (hi : LeftInv Γ φ) (h : IntegrableOn φ (stdDom Γ) μ) :
    Integrable (descend Γ φ) (quotMeasure Γ μ) ∧
      ∫ q, descend Γ φ q ∂quotMeasure Γ μ = ∫ x in stdDom Γ, φ x ∂μ := by
  have e : descend Γ φ = φ ∘ sec Γ := funext fun q => by
    rw [Function.comp_apply, ← hi.descend_mk, mk_sec]
  rw [e]
  exact ⟨(measurePreserving_sec.integrable_comp_emb measurableEmbedding_sec).2 h,
    measurePreserving_sec.integral_comp measurableEmbedding_sec φ⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_tensor {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    Continuous (tensor σ J fa ff) ∧ HasCompactSupport (tensor σ J fa ff) := by
  have hb := hf.tensorFin_mem
  have h1 : Continuous (tensorInf σ J fa) :=
    continuous_finset_prod _ fun w _ => (ha w).1.comp (continuous_projInfArch σ J w)
  have h2 : HasCompactSupport (tensorInf σ J fa) := by
    refine .intro ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_univ_pi fun w => (ha w).2)) fun g hg => ?_
    by_contra hne
    exact hg fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 hne w (Finset.mem_univ w))
  rw [tensor_eq_infFin]
  refine ⟨(h1.comp (continuous_projInf σ J)).mul (hb.1.continuous.comp (continuous_projFin σ J)), .intro
    ((infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod h2 hb.2)) fun g hg => ?_⟩
  by_contra hne
  exact hg ⟨subset_tsupport _ (left_ne_zero_of_mul hne), subset_tsupport _ (right_ne_zero_of_mul hne)⟩

theorem isMulCommutative_cent_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) : IsMulCommutative (cent (ratEmb σ J γ)) :=
  ⟨⟨fun a b => Subtype.ext (GAd_ext σ J
    (fun w => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).1.1
          (centMap (projArch σ J w) _ a) (centMap (projArch σ J w) _ b)))
    fun v => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).1.1
          (centMap (proj σ J v) _ a) (centMap (proj σ J v) _ b)))⟩⟩

theorem class_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) (qa : ∀ w : InfinitePlace F, XSet P w.Completion J), (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v).1) → (∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w).1) → Integrable (descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * ((∏ᶠ v, orbCls (μf v) (dtf v) (ff v) (qf v)) * ∏ w, orbCls (μa w) (dta w) (fa w) (qa w)) := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt γ hγ qf qa hqf hqa
  have hreg : IsRegSS γ.1.1 := by
    rw [IsRegSS, hγ]; exact P.2.2.1.separable
  obtain ⟨ea, ef, e, hc, ⟨𝓣, h𝓣, hvol⟩, hf, ha⟩ := GlobalTheory.T.exists_centralizer_measures_from_unitaryTorus F E σ hcm r P J hJ L γ hγ dta dtf dt hdt
  obtain ⟨pf, pa⟩ := GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ
  have := hμ.haar
  have := hc.1
  have := hc.2.1
  have := hc.2.2.1
  have : ∀ w, (ea w).IsMulRightInvariant := fun w =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hreg w)) _
  have : ∀ v, (ef v).IsMulRightInvariant := fun v =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hreg v)) _
  have hf' : ∀ v, HasOrbInt (μf v) (proj σ J v (ratEmb σ J γ)) (ef v) (ff v) (orbCls (μf v) (dtf v) (ff v) (qf v)) :=
    fun v => by
      obtain ⟨x, φ, h, e1, e2⟩ := hqf v
      have := (pf v (μf v) (dtf v) (ff v) (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) (hff.1 v).1.continuous
        (hff.1 v).2).2 x φ h
      rw [show qf v = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
      exact (hf v x φ h e2 _ _ _).1 this
  have ha' : ∀ w, HasOrbInt (μa w) (projArch σ J w (ratEmb σ J γ)) (ea w) (fa w)
      (orbCls (μa w) (dta w) (fa w) (qa w)) := fun w => by
    obtain ⟨x, φ, h, e1, e2⟩ := hqa w
    have := (pa w (μa w) (dta w) (fa w) (hμ.haar_arch w) (IsRestrictedProd.haar_arch hdt w) (hfa w).1
      (hfa w).2).2 x φ h
    rw [show qa w = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
    exact (ha w x φ h e2 _ _ _).1 this
  have hO := (hasOrbInt_tensor_of_hasOrbInt hμ hc hff.2 (eventually_conj_mem_stabLoc hcm hJ L hreg) ha' hf').2
  have hfin := (GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume F E σ hcm r P).2 dt (IsRestrictedProd.haar hdt)
  have ht := continuous_tensor hfa hff
  obtain ⟨-, h1, h2⟩ := GlobalTheory.T.classTerm_eq_volume_mul_orbitalIntegral (GAd σ J) (ratPts σ J) (ratEmb σ J γ) (range_ratEmb σ J ▸ ⟨γ, rfl⟩)
    (isMulCommutative_cent_ratEmb hreg) μ e 𝓣 h𝓣 (hvol ▸ hfin.lt_top) _ _ ht.1 ht.2 hO _
    (isFundamentalDomain_stdDom _ μ)
  obtain ⟨h3, h4⟩ := integrable_descend_of_stdDom
    (fun g hg x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul (ratEmb σ J γ) (tensor σ J fa ff) hg x) h1
  refine ⟨h3, ?_⟩
  rw [h4, h2, Measure.real, hvol, mul_comm (∏ w, _)]

end GlobalTheory.TrClassTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionSplitProductDatumIsPureTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_splitProductDatum_isPureTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (ι : Type) (s : Finset ι) (v : ι → FinPl D) (a : ι → AE D), (∀ i ∈ s, IsSplitIdem D (a i) ∧ a i + cA D (a i) = idem D (.inl (v i))) → Set.InjOn v s → ∀ Φ : ι → WO S T → ℂ, (∀ i ∈ s, IsSBHalf (a i) (latO S T ΛS ΛT fun _ => True) (Φ i)) → ∀ (x : Place D → WO S T → ℂ) (f Ψ : WO S T → ℂ), (∀ i ∈ s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i) (x (.inl (v i)))) → (∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀) → (∀ t, IsHalf (∑ i ∈ s, a i) t → Ψ t = ∏ i ∈ s, Φ i (a i • t)) → (∀ t, ¬ IsHalf (∑ i ∈ s, a i) t → Ψ t = 0) → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i ∈ s, a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Ψ f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  first | exact @GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure | exact GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure | (intros; apply GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure <;> assumption)
end

