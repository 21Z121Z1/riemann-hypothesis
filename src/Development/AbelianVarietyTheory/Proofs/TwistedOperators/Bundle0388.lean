import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteA
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LocCompFin

open GlobalTheory.CuspRep.LocEx GlobalTheory.AutMult

section Groups

variable {D : D7} (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  GlobalTheory.AdelicU.proj_emb_self _ _ u x

theorem commute_locFin (x : Gv V u) {g : GfC V} (hg : finLoc V u g = 1) : Commute (locFin V u x) g :=
  Subtype.ext (GlobalTheory.AdelicU.commute_emb _ _ x hg).eq

theorem continuous_locFin : Continuous (locFin V u) :=
  (GlobalTheory.AdelicU.continuous_emb _ _ u).subtype_mk _

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (GlobalTheory.AdelicU.continuous_proj _ _ u).comp continuous_subtype_val

theorem finLoc_inv_mul (g : GfC V) : finLoc V u ((locFin V u (finLoc V u g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, finLoc_locFin, inv_mul_cancel]

end Groups

theorem exists_locComp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N),
      π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  intro D V u W _ _ σ hirr hadm
  obtain ⟨hnt, hinv⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr
  obtain ⟨x, hx0⟩ := exists_ne (0 : W)
  have hsplit : ∀ g (y : W), σ g y = σ (locFin V u (finLoc V u g)) (σ ((locFin V u (finLoc V u g))⁻¹ * g) y) :=
    fun g y => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hcomm : ∀ g : GfC V, finLoc V u g = 1 → ∀ h (y : W),
      σ g (σ (locFin V u h) y) = σ (locFin V u h) (σ g y) := by
    intro g hg h y
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin V u h hg).eq, map_mul, Module.End.mul_apply]
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun v => (hadm.1 v).preimage (continuous_locFin V u)
  let K₀ : Subgroup (GfC V) := stab σ x
  have hK₀ : IsOpen (K₀ : Set (GfC V)) := hadm.1 x
  let Kc : Subgroup (Gv V u) := K₀.comap (locFin V u) ⊓ Kv V u
  have hKco : IsOpen (Kc : Set (Gv V u)) :=
    (hK₀.preimage (continuous_locFin V u)).inter (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ u)
  have hKcc : IsCompact (Kc : Set (Gv V u)) :=
    (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ u).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKco) fun k hk => hk.2
  have hKcK₀ : ∀ k ∈ Kc, locFin V u k ∈ K₀ := fun k hk => hk.1
  have hxKc : x ∈ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc := mem_fix.2 fun k hk => hKcK₀ k hk
  have hnull : nullPart (σ.comp (locFin V u)) Kc = ⊥ := by
    rcases hinv (nullPart (σ.comp (locFin V u)) Kc) (fun g y hy => by
      rw [hsplit g y]
      exact nullPart_act _ Kc (finLoc V u g) (nullPart_comm _ Kc (σ _)
        (fun h z => hcomm _ (finLoc_inv_mul V u g) h z) hy)) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_nullPart hρ hKcc hxKc (h ▸ Submodule.mem_top)) hx0
  have h2 : ∀ Y : Submodule ℂ W, (∀ g, ∀ v ∈ Y, σ.comp (locFin V u) g v ∈ Y) →
      Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc = ⊥ → Y = ⊥ :=
    fun Y hY h => le_bot_iff.1 (hnull ▸ le_nullPart hρ hKcc Y hY h)
  let L' : Subgroup (GfC V) := K₀ ⊓ (finLoc V u).ker
  let U : Submodule ℂ W := GlobalTheory.PRep.fixed σ L'
  have hU : ∀ g, ∀ v ∈ U, σ.comp (locFin V u) g v ∈ U := fun g v hv => mem_fix.2 fun k hk => by
    change σ k (σ (locFin V u g) v) = σ (locFin V u g) v
    rw [hcomm k hk.2 g v, mem_fix.1 hv k hk]
  have hU0 : U ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hk.1, hx0⟩
  obtain ⟨C, hCo, hCc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfin : ∀ K' : Subgroup (Gv V u), IsOpen (K' : Set (Gv V u)) →
      FiniteDimensional ℂ ↥(U ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) K') := by
    intro K' hK'
    let M : Subgroup (GfC V) := (K₀ ⊓ (Kc ⊓ K').comap (finLoc V u)) ⊓ C
    have hMo : IsOpen (M : Set (GfC V)) :=
      (hK₀.inter ((hKco.inter hK').preimage (continuous_finLoc V u))).inter hCo
    have hMc : IsCompact (M : Set (GfC V)) :=
      hCc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hMo) fun k hk => hk.2
    have := hadm.2 M hMo hMc
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.PRep.fixed σ M) fun v hv => mem_fix.2 fun k hk => ?_
    have hk1 : (locFin V u (finLoc V u k))⁻¹ * k ∈ L' :=
      ⟨K₀.mul_mem (K₀.inv_mem (hKcK₀ _ hk.1.2.1)) hk.1.1, finLoc_inv_mul V u k⟩
    rw [hsplit k v, mem_fix.1 hv.1 _ hk1]
    exact mem_fix.1 hv.2 _ hk.1.2.2
  obtain ⟨π, ⟨f, hf0, hf⟩, hπ⟩ := exists_irred hρ hKco h2 U hU hU0 hfin
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.irred, hπ, ?_⟩
  let F : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }
  have hI : ∀ g, ∀ y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)), σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)) := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u))) hy ?_ ?_ ?_
    · rintro T _ ⟨z, rfl⟩
      let T' : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
        { toLinearMap := σ ((locFin V u (finLoc V u g))⁻¹ * g) ∘ₗ T.toLinearMap
          isIntertwining' := fun h => LinearMap.ext fun w => by
            change σ _ (T (π.ρ h w)) = σ (locFin V u h) (σ _ (T w))
            rw [T.isIntertwining]
            exact hcomm _ (finLoc_inv_mul V u g) h _ }
      refine Submodule.mem_iSup_of_mem T' ⟨π.ρ (finLoc V u g) z, ?_⟩
      change T' (π.ρ (finLoc V u g) z) = σ g (T z)
      rw [T'.isIntertwining, hsplit g (T z)]
      rfl
    · simp only [map_zero]; exact zero_mem _
    · intro a b ha hb; simp only [map_add]; exact add_mem ha hb
  rcases hinv _ hI with h | h
  · refine absurd ?_ hf0
    have hr : LinearMap.range F.toLinearMap ≤ ⊥ :=
      h ▸ le_iSup (fun T : π.ρ.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range T.toLinearMap) F
    exact LinearMap.range_eq_bot.1 (le_bot_iff.1 hr)
  · exact h

end GlobalTheory.LocCompFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem exists_basis_in_lattice {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) [hΛ : Λ.IsLattice K] (N : ℕ) (hN : 2 ≤ N) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), (∀ i, b i ∈ Λ) ∧ ∃ c : 𝓞 K, IsCoprime c (N : 𝓞 K) ∧
      ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ.fg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  haveI : IsAddTorsionFree Λ := ⟨fun k hk a b h => Subtype.ext
    (IsAddTorsionFree.nsmul_right_injective hk (by simpa using congrArg Subtype.val h))⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.CoprimeBasis.exists_coprime_basis K Λ N hN
  set x' : Fin r → (Fin n → K) := fun i => (x i : Fin n → K) with hx'
  have hli' : LinearIndependent (𝓞 K) x' := hli.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliK : LinearIndependent K x' := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hli'
  have hmem : ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range x') := by
    intro w hw
    have h := Submodule.mem_map_of_mem (f := Λ.subtype) (hspan ⟨w, hw⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have e : (Λ.subtype (c • (⟨w, hw⟩ : Λ))) = (c : K) • w := by
      simp [Submodule.coe_smul, algebraMap_smul]
    rw [e] at h
    exact h
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hspanK : ⊤ ≤ Submodule.span K (Set.range x') := by
    rw [← hΛ.span_eq_top, Submodule.span_le]
    intro w hw
    have h1 := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range x') (hmem w hw)
    have h2 := Submodule.smul_mem (Submodule.span K (Set.range x')) (c : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcK, one_smul] at h2
  let b0 : Module.Basis (Fin r) K (Fin n → K) := Module.Basis.mk hliK hspanK
  have hr : r = n := by
    have := Module.finrank_eq_card_basis b0
    simpa using this.symm
  subst hr
  refine ⟨b0, fun i => ?_, c, hcop, fun w hw => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (x i).2
  · have : Set.range b0 = Set.range x' := by rw [Module.Basis.coe_mk]
    rw [this]; exact hmem w hw

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

open Matrix in

theorem exists_onto_mod {n n' : ℕ} (hnn : n ≤ n') (Λ : Submodule (𝓞 K) (Fin n → K)) (Λ' : Submodule (𝓞 K) (Fin n' → K))
    [Λ.IsLattice K] [Λ'.IsLattice K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ x : Matrix (Fin n) (Fin n') K, (∀ w ∈ Λ', x *ᵥ w ∈ Λ) ∧ ∃ y : Matrix (Fin n') (Fin n) K, (∀ v ∈ Λ, y *ᵥ v ∈ Λ') ∧
      ∃ a ∈ 𝔪, x * y - 1 = (a : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  set N : ℕ := 2 * Ideal.absNorm 𝔪 with hNdef
  have hN0 : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hN : 2 ≤ N := by omega
  have hNm : (N : 𝓞 K) ∈ 𝔪 := by
    rw [hNdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem 𝔪)
  obtain ⟨b, hb, c, hc, hcb⟩ := exists_basis_in_lattice Λ N hN
  obtain ⟨b', hb', c', hc', hcb'⟩ := exists_basis_in_lattice Λ' N hN
  obtain ⟨u, v, huv⟩ := hc.mul_left hc'
  let φ : (Fin n' → K) →ₗ[K] (Fin n → K) := b'.constr K fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else 0
  let ψ : (Fin n → K) →ₗ[K] (Fin n' → K) := b.constr K fun i => b' (Fin.castLE hnn i)
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    refine b.ext fun i => ?_
    show φ (ψ (b i)) = b i
    simp only [φ, ψ, Module.Basis.constr_basis, Fin.coe_castLE]
    rw [dif_pos i.isLt]
  have hφ : Submodule.span (𝓞 K) (Set.range b') ≤ Λ.comap (φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show φ (b' j) ∈ Λ
    simp only [φ, Module.Basis.constr_basis]
    split_ifs
    · exact hb _
    · exact Λ.zero_mem
  have hψ : Submodule.span (𝓞 K) (Set.range b) ≤ Λ'.comap (ψ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ψ (b i) ∈ Λ'
    simp only [ψ, Module.Basis.constr_basis]
    exact hb' _
  refine ⟨LinearMap.toMatrix' (((u * c' : 𝓞 K) : K) • φ), fun w hw => ?_,
    LinearMap.toMatrix' ((c : K) • ψ), fun w hw => ?_, u * c * c' - 1, ?_, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply]
    have h1 : φ ((c' : K) • w) ∈ Λ := hφ (hcb' w hw)
    have h2 := Λ.smul_mem u h1
    rw [← algebraMap_smul K u, map_smul, smul_smul] at h2
    convert h2 using 2
    push_cast; ring
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply, ← map_smul]
    exact hψ (hcb w hw)
  · have : u * c * c' - 1 = -(v * (N : 𝓞 K)) := by linear_combination huv
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hNm)
  · rw [← LinearMap.toMatrix'_comp]
    have e : (((u * c' : 𝓞 K) : K) • φ) ∘ₗ ((c : K) • ψ) = ((u * c * c' : 𝓞 K) : K) • LinearMap.id := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, hφψ, smul_smul]
      congr 1; push_cast; ring
    rw [e, map_smul, LinearMap.toMatrix'_id]
    push_cast
    rw [sub_smul, one_smul]

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField Matrix

theorem ontoModEx : OntoModEx := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have h0 := G.sp.P_is i hi.le
  have h1 := G.sp.P_is (i + 1) hi
  haveI : (G.Λ (.core i)).IsLattice D.host.E := h0.sd.1
  haveI : (G.Λ (.core (i + 1))).IsLattice D.host.E := h1.sd.1
  have e0 : (G.V (.core i)).rank = rankP D i := h0.rank
  have e1 : (G.V (.core (i + 1))).rank = rankP D (i + 1) := h1.rank
  have hle : (G.V (.core i)).rank ≤ (G.V (.core (i + 1))).rank := by
    rw [e0, e1]; unfold rankP; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
  obtain ⟨x, hx, y, hy, a, ha, hxy⟩ :=
    exists_onto_mod hle (G.Λ (.core i)) (G.Λ (.core (i + 1))) G.modul (G.pl.modul_ne_bot sc)
  refine ⟨x, hx, y, hy, ?_⟩
  have h1m : (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) ∈
      homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun v hv => by simpa using hv
  have e : x * y - 1 = a • (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) := by
    rw [hxy]; exact algebraMap_smul D.host.E a _
  rw [e]
  exact Submodule.smul_mem_smul ha h1m

end GlobalTheory.OntoModPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLieOp

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.RealLift

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem actsD_zero' (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

open scoped Classical in

theorem actsD_comb (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f + g) ⇑(c • f₁ + g₁) := by
  have e : ∀ (r : (κ → AF F) → ℂ) (φ ψ : SInf F κ),
      tens (evI F) ⇑(c • φ + ψ) r = c • tens (evI F) ⇑φ r + tens (evI F) ⇑ψ r := by
    intro r φ ψ; funext y; simp [tens]; ring
  have key : ∀ r, Rest (evI F) ⇑f r → Rest (evI F) ⇑g r → ∀ x,
      HasDerivAt (fun t => L t (tens (evI F) ⇑(c • f + g) r) x) (tens (evI F) ⇑(c • f₁ + g₁) r x) 0 := by
    intro r h1 h2 x
    rw [e, e]
    have h := ((hf r h1 x).const_mul c).add (hg r h2 x)
    have hfun : (fun t => L t (c • tens (evI F) ⇑f r + tens (evI F) ⇑g r) x) =
        (fun t => c * L t (tens (evI F) ⇑f r) x) + (fun t => L t (tens (evI F) ⇑g r) x) := by
      funext t; simp [map_add, map_smul]
    rw [hfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h

  set g₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl
  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀ := fun φ =>
    ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  intro r hr x
  by_cases h0 : c • f + g = 0
  · have hz : c • f₁ + g₁ = 0 := by
      ext a
      have h := key r₀ (hrest₀ f) (hrest₀ g) (ptAt a 0)
      rw [h0, hzeroT] at h
      simp only [map_zero, Pi.zero_apply] at h
      have h' := h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      rw [htens₀, pureA_ptAt, hg₀0, mul_one] at h'
      simpa using h'
    rw [h0, hz, hzeroT]
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · have hR : (fun y => r (fun i => ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F), y i))) ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :=
      mem_SB_of_pureA_mem h0 (tens_eq_pureA _ hr.1 ▸ hr.2)
    have hrest : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r := fun φ =>
      ⟨hr.1, by rw [tens_eq_pureA _ hr.1]; exact Submodule.subset_span ⟨φ, _, hR, rfl⟩⟩
    exact key r (hrest f) (hrest g) x

theorem actsD_add (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(f + g) ⇑(f₁ + g₁) := by
  simpa only [one_smul] using actsD_comb L 1 hf hg

theorem actsD_smul (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f) ⇑(c • f₁) := by
  simpa only [add_zero] using actsD_comb L c hf (actsD_zero' L)

end GlobalTheory.RealLieOp

theorem GlobalTheory.RealLieOp.exists_realOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∃ T : Module.End ℂ R.Pi,
      (∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f₁ = T (R.p f)) ∧
      ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p' f₁' = T (R.p' f') := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM γ hγ
  let L : ℝ → Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := fun t => om (1, γ (Multiplicative.ofAdd t))
  let L' : ℝ → Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := fun t => om' (1, γ (Multiplicative.ofAdd t))
  let S : Set (R.Pi × R.Pi) :=
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ z = (R.p f, R.p f₁)} ∪
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')), f ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f ⇑f₁ ∧ z = (R.p' f, R.p' f₁)}
  have hspan : ∀ z ∈ Submodule.span ℂ S, ∃ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (f' f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f' ⇑f₁' ∧
      z = (R.p f + R.p' f', R.p f₁ + R.p' f₁') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨f, f₁, hf, h1, rfl⟩ | ⟨f, f₁, hf, h1, rfl⟩
      · exact ⟨f, f₁, 0, 0, hf, h1, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', by simp⟩
      · exact ⟨0, 0, f, f₁, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, hf, h1, by simp⟩
    | zero => exact ⟨0, 0, 0, 0, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', Prod.ext (by simp) (by simp)⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      obtain ⟨g, g₁, g', g₁', hg, h2, hg', h2', rfl⟩ := hy
      refine ⟨f + g, f₁ + g₁, f' + g', f₁' + g₁', add_mem hf hg, GlobalTheory.RealLieOp.actsD_add L h1 h2,
        add_mem hf' hg', GlobalTheory.RealLieOp.actsD_add L' h1' h2', ?_⟩
      simp only [map_add, Prod.mk_add_mk]
      abel_nf
    | smul c x _ hx =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      refine ⟨c • f, c • f₁, c • f', c • f₁', Submodule.smul_mem _ c hf, GlobalTheory.RealLieOp.actsD_smul L c h1,
        Submodule.smul_mem _ c hf', GlobalTheory.RealLieOp.actsD_smul L' c h1', ?_⟩
      simp only [map_smul, Prod.smul_mk, smul_add]
  have hgraph : ∀ z ∈ Submodule.span ℂ S, z.1 = 0 → z.2 = 0 := by
    intro z hz hz0
    obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hspan z hz
    have e : R.p f + R.p' f' = 0 := hz0
    have e2 : R.p f = R.p' (-f') := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left e
    have hn : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑(-f') ⇑(-f₁') := by
      simpa only [neg_one_smul] using GlobalTheory.RealLieOp.actsD_smul L' (-1) h1'
    have := hM.real.lie γ hγ f hf (-f') (neg_mem hf') f₁ (-f₁') h1 hn e2
    show R.p f₁ + R.p' f₁' = 0
    rw [this, map_neg, neg_add_cancel]
  obtain ⟨T, hT⟩ := LinearMap.exists_extend (Submodule.span ℂ S).toLinearPMap.toFun
  have hT' : ∀ z ∈ Submodule.span ℂ S, T z.1 = z.2 := by
    intro z hz
    have hz' : z ∈ (Submodule.span ℂ S).toLinearPMap.graph := by
      rw [Submodule.toLinearPMap_graph_eq _ hgraph]; exact hz
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hz'
    rw [← hy1, ← hy2]
    exact LinearMap.congr_fun hT y
  refine ⟨T, fun f hf f₁ h1 => ?_, fun f hf f₁ h1 => ?_⟩
  · exact (hT' (R.p f, R.p f₁) (Submodule.subset_span (Or.inl ⟨f, f₁, hf, h1, rfl⟩))).symm
  · exact (hT' (R.p' f, R.p' f₁) (Submodule.subset_span (Or.inr ⟨f, f₁, hf, h1, rfl⟩))).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKMapExtensionLevelCharacterCovariantStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gKMap_extension_level_character_covariant : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ → ∀ T : MMap M, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  first | exact @GlobalTheory.GKExtLevel.lev | exact GlobalTheory.GKExtLevel.lev | (intros; apply GlobalTheory.GKExtLevel.lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUniqueStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_pair_spherical_vector_unique : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ → ∀ x ∈ fixed ρ K, x ≠ 0 → fixed ρ K = ℂ ∙ x := by
  first | exact @GlobalTheory.fixed_eq_span_of_gelfandPair | exact GlobalTheory.fixed_eq_span_of_gelfandPair | (intros; apply GlobalTheory.fixed_eq_span_of_gelfandPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnitsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_above_place_of_trivial_units : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  first | exact @GlobalTheory.UnrOverPlace.unrAt_of_unramAt | exact GlobalTheory.UnrOverPlace.unrAt_of_unramAt | (intros; apply GlobalTheory.UnrOverPlace.unrAt_of_unramAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  first | exact @GlobalTheory.HeckeFinRam.finite_ramified | exact GlobalTheory.HeckeFinRam.finite_ramified | (intros; apply GlobalTheory.HeckeFinRam.finite_ramified <;> assumption)
end

