import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0348
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0350
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedFirstCondition
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem hecke_dominant_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hIw hpos V _ _ π hπ t t' ht ht' T T' hT hT' v l hl
  obtain ⟨r, hr, x, hxN, hx⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hIw hpos t' ht'
  have hxJ : ∀ i, x i ∈ J := fun i => (hxN i).1
  have hform := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ _ T' hT' r x hr hxJ hx v
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set g := leviEmb k (stdBlocks d hd) t with hg
  set g' := leviEmb k (stdBlocks d hd) t' with hg'
  have hmul : leviEmb k (stdBlocks d hd) (t * t') = g * g' := map_mul _ _ _
  have hterm : ∀ i, l (π g (π (x i * g') (v : V))) = l (π (g * g') (v : V)) := by
    intro i
    have hc : g * x i * g⁻¹ ∈ J := (ht.1 _ (hxN i)).1
    have hfac : g * (x i * g') = (g * x i * g⁻¹) * (g * g') := by group
    have h1 : l (π (g * x i * g⁻¹) (π (g * g') (v : V))) = l (π (g * g') (v : V)) :=
      LinearMap.congr_fun (hl _ hc) _
    rw [← Module.End.mul_apply, ← map_mul, hfac, map_mul, Module.End.mul_apply, h1]
  have hTT : l (((T * T') v : fixed π J) : V) = l (π g ((T' v : fixed π J) : V)) :=
    (hT (T' v) l hl).symm
  rw [hTT, hform, hmul, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeCompatHolds
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem jacquet_hecke_operator_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ t ht T hT v
  obtain ⟨r, hr, x, hx, hu⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hI hpos t ht
  have key := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ (leviEmb k (stdBlocks d hd) t) T hT r x hr
    (fun i => (hx i).1) hu v
  have hmk : ∀ i, (Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    intro i
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨x i, (hx i).2⟩, π (leviEmb k (stdBlocks d hd) t) (v : V), ?_⟩
    simp [map_mul]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have hsum : (Submodule.Quotient.mk ((T v : fixed π J) : V) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    rw [key, Submodule.Quotient.mk_smul]
    have h2 : (Submodule.Quotient.mk (∑ i, π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
        ∑ i : Fin r, Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :=
      map_sum (Submodule.mkQ _) _ _
    rw [h2, Finset.sum_congr rfl fun i _ => hmk i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [hsum, jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltration
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoAssembly

def equivComp {G H V V' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') (ψ : H →* G) : Representation.Equiv (ρ.comp ψ) (ρ'.comp ψ) :=
  Representation.Equiv.mk' ⟨e.toLinearEquiv.toLinearMap, fun h => by
      ext x; exact LinearMap.congr_fun (e.isIntertwining' (ψ h)) x⟩ e.invFun
    e.left_inv e.right_inv

set_option maxHeartbeats 1000000 in

theorem jacquetOfInducedFiltration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  intro k _ _ _ _ α β n _ _ _ _ _ _ m _ _ m' _ _ e e'
  let N := Fintype.card n
  let ι : n ≃ Fin N := Fintype.equivFin n
  let E := e.trans ι
  let E' := e'.trans ι
  obtain ⟨βF, hβ⟩ := GlobalTheory.T.exists_strict_block_order m E
  obtain ⟨γF, hγ⟩ := GlobalTheory.T.exists_strict_block_order m' E'
  obtain ⟨φ, hφ, -, hφsc⟩ := GlobalTheory.T.levi_block_homeomorph k E βF hβ
  obtain ⟨φ', hφ', -, -⟩ := GlobalTheory.T.levi_block_homeomorph k E' γF hγ
  obtain ⟨K, w, hcov, hfilt⟩ := GlobalTheory.T.bernstein_zelevinsky_geometric_lemma k N βF γF
  let sz : Equiv.Perm (Fin N) → α → β → ℕ := fun v i j =>
    (Finset.univ.filter fun x : Fin N => blk E x = i ∧ blk E' (v.symm x) = j).card
  let toSM : Fin K → SizeMatrix m m' := fun t => ⟨sz (w t), GlobalTheory.T.permutation_block_counts E E' (w t)⟩
  have hsz : ∀ v v' : Equiv.Perm (Fin N), permGL k v' ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) ↔ sz v = sz v' := by
    intro v v'
    rw [GlobalTheory.T.double_coset_block_matrix k E βF hβ E' γF hγ v v']
    exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => congrFun (congrFun h i) j⟩
  have hself : ∀ v : Equiv.Perm (Fin N), permGL k v ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) := fun v =>
    (hsz v v).2 rfl
  have inj : Function.Injective toSM := by
    intro t t' h
    have h1 : sz (w t) = sz (w t') := congrArg Subtype.val h
    obtain ⟨j, -, huniq⟩ := hcov (permGL k (w t'))
    exact (huniq t ((hsz _ _).2 h1)).trans (huniq t' (hself _)).symm
  have surj : Function.Surjective toSM := by
    intro B
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_perm_block_matrix E E' B
    obtain ⟨t, ht, -⟩ := hcov (permGL k v)
    refine ⟨t, Subtype.ext ?_⟩
    show sz (w t) = B.1
    rw [(hsz _ _).1 ht]
    exact funext fun i => funext fun j => hv i j
  refine ⟨K, Equiv.ofBijective toSM ⟨inj, surj⟩, ?_⟩
  intro W _ _ ρ hρ
  let σ := ρ.comp φ.symm.toMonoidHom
  have hσ : GroundTheory.Automorphic.IsSmooth σ := GlobalTheory.T.isSmooth_comp_continuous φ.symm.toMonoidHom hφsc ρ hρ
  have hF := hfilt W σ hσ
  obtain ⟨V, hF⟩ := hF
  obtain ⟨hV0, hF⟩ := hF
  obtain ⟨hVK, hF⟩ := hF
  obtain ⟨hVmono, hV, hΨ⟩ := hF
  have e1' := GlobalTheory.T.induction_reindex_equiv k e e' ι ρ
  obtain ⟨e1⟩ := e1'
  have e2' := GlobalTheory.T.jac_equiv_jacquetRep_comp_levi_equiv k E' γF hγ φ' hφ' (V := IndSp E ρ) (parInd E ρ)
  obtain ⟨e2⟩ := e2'
  have e3' := GlobalTheory.T.parabolicInd_equiv_levi_transport k E βF hβ φ hφ ρ
  obtain ⟨e3⟩ := e3'
  have e4' := GlobalTheory.T.jacquet_module_equiv k N γF (V := IndSp E ρ) (parInd E ρ) _ e3
  obtain ⟨e4⟩ := e4'
  have e12 := e1.trans e2
  have e45 := equivComp e4 φ'.toMonoidHom
  have e5 := e12.trans e45
  have hT := GlobalTheory.T.filtration_transport_equiv φ'.toMonoidHom _ _ e5 K _
    (fun j => indRep (cellLeviSub k βF γF (w j)) (normInducing σ γF (w j))) V hV0 hVK hVmono hV hΨ
  obtain ⟨S, hT⟩ := hT
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hT
  refine ⟨S, hS1, hS2, hS3, fun t f g => ?_⟩
  have q1' := hS4 t
  obtain ⟨q1⟩ := q1'
  have c' := GlobalTheory.T.levi_intersection_conjugate k E βF hβ φ hφ E' γF hγ φ' hφ' ρ (w t)
  obtain ⟨f0, g0, c'⟩ := c'
  obtain ⟨q2⟩ := c'
  have q3' := GlobalTheory.T.cell_levi_tensor_decomposition (fun i j => by rw [Fintype.card_fin, Fintype.card_fin]; rfl) f0 g0 f g ρ
  obtain ⟨q3⟩ := q3'
  exact ⟨q1.trans (q2.trans q3)⟩

end GlobalTheory.CompanionTheory.GeoAssembly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHolds
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem jacquet_projection_hecke_intertwines : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    PositivityTheory.SphericalProduct.A2 G := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v
  obtain ⟨r, hr, x, hxJN, hx⟩ := GlobalTheory.T.dominant_coset_reps_unipotent G D t ht
  have hUv := GlobalTheory.T.hecke_operator_coset_formula G D.J D.isOpen_J D.isCompact_J V π hπ (t : G) U hU r x hr
    (fun i => (hxJN i).1) hx v
  have hstep : ∀ i, (Submodule.Quotient.mk (π (x i * (t : G)) (v : V)) : GlobalTheory.PRep.Jacquet π D.N) =
      Submodule.Quotient.mk (π (t : G) (v : V)) := by
    intro i
    refine (Submodule.Quotient.eq _).mpr (Submodule.subset_span ⟨⟨x i, (hxJN i).2⟩, π (t : G) (v : V), ?_⟩)
    simp
  have hsum := map_sum (Submodule.mkQ (GlobalTheory.PRep.twKer π D.N 1))
    (fun i => π (x i * (t : G)) (v : V)) Finset.univ
  simp only [Submodule.mkQ_apply] at hsum
  show (Submodule.Quotient.mk (↑(U v)) : GlobalTheory.PRep.Jacquet π D.N) =
    (D.piN π t) (Submodule.Quotient.mk (v : V))
  rw [hUv, Submodule.Quotient.mk_smul, hsum]
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), one_smul]
  rfl

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHolds
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.CompanionTheory.ThetaProd
open scoped Matrix

namespace GlobalTheory.CompanionTheory.JmThetaInv

section Ring

variable {A : Type} [CommRing A]

theorem thetaL_eq_one {h : ℕ} (d : Fin h → ℕ) {x : Levi A (fun a => Fin (d a))} (hx : thetaL d x = 1) : x = 1 := by
  funext b
  obtain ⟨c, rfl⟩ := Fin.rev_surjective b
  have h1 : thetaW A (d (Fin.rev c)) (x (Fin.rev c)) = 1 := congrFun hx c
  have h2 := GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring _ (x (Fin.rev c))
  rw [h1, map_one] at h2
  exact h2.symm

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := A) d) := by
  intro y
  refine ⟨fun b => thetaW A (d b) (cast (by show GL (Fin (d (Fin.rev (Fin.rev b)))) A = _; rw [Fin.rev_rev]) (y (Fin.rev b))), ?_⟩
  funext a
  show thetaW A (d (Fin.rev a)) (thetaW A (d (Fin.rev a)) (cast _ (y (Fin.rev (Fin.rev a))))) = y a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring]
  have : ∀ (c : Fin h) (hc : c = a) (hh : GL (Fin (d (Fin.rev c))) A = GL (Fin (d (Fin.rev a))) A),
      cast hh (y c) = y a := by
    rintro c rfl hh
    rfl
  exact this _ (Fin.rev_rev a) _

theorem thetaW_mem_unipRad_iff {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : GL (Fin N) A) :
    thetaW A N g ∈ unipRad A (stdBlocks (fun a => d (Fin.rev a)) hd') ↔ g ∈ unipRad A (stdBlocks d hd) := by
  constructor
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) :=
      (thetaW_mem_parab_iff d hd hd' g).1 (unipRad_le_parab A _ H)
    refine (coe_mem_unipRad A (⟨g, hp⟩ : parab A (stdBlocks d hd))).2 (thetaL_eq_one d ?_)
    rw [← leviProj_thetaW d hd hd' ⟨g, hp⟩]
    exact (coe_mem_unipRad A _).1 H
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) := unipRad_le_parab A _ H
    have h1 : leviProj A (stdBlocks d hd) ⟨g, hp⟩ = 1 := (coe_mem_unipRad A _).1 H
    refine (coe_mem_unipRad A (⟨thetaW A N g, (thetaW_mem_parab_iff d hd hd' g).2 hp⟩ :
      parab A (stdBlocks (fun a => d (Fin.rev a)) hd'))).2 ?_
    rw [leviProj_thetaW d hd hd' ⟨g, hp⟩, h1, map_one]

theorem thetaW_leviEmb {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : Levi A (fun a => Fin (d a))) :
    thetaW A N (leviEmb A (stdBlocks d hd) g) =
      leviEmb A (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective j
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply, rev_stdBlocks d hd hd', rev_stdBlocks d hd hd', ← map_inv]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same]
    show _ = (thetaW A (d (Fin.rev a)) (g (Fin.rev a))).1 i j
    rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply]
    rfl
  · rw [leviEmb_apply_ne A _ _ (fun hh => hab (Fin.rev_injective hh).symm), leviEmb_apply_ne A _ _ hab]

end Ring

section Jacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twKer_comp_thetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    twKer (π.comp (thetaW k N)) (unipRad k (stdBlocks d hd)) 1 =
      twKer π (unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd')) 1 := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨thetaW k N u, (thetaW_mem_unipRad_iff d hd hd' _).2 u.2⟩, v, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have hu : thetaW k N (u : GL (Fin N) k) ∈ unipRad k (stdBlocks d hd) :=
      (thetaW_mem_unipRad_iff d hd hd' _).1 (by rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]; exact u.2)
    refine Submodule.subset_span ⟨⟨_, hu⟩, v, ?_⟩
    simp [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]

def jacCompThetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    (jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d)) :=
  .mk (Submodule.quotEquivOfEq _ _ (twKer_comp_thetaW d hd hd' π)) fun g => by
    refine LinearMap.ext fun v => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply]
    rw [Submodule.quotEquivOfEq_mk, jac_mk, jac_mk, map_smul, Submodule.quotEquivOfEq_mk, deltaHalf_thetaL]
    simp only [MonoidHom.comp_apply, thetaW_leviEmb d hd hd' g]

theorem jm_comp_theta_eq_dual_reverse (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm (dualRev hA x) (sum_dualRev hA x hd) π := by
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := sum_dualRev hA x hd
  have T1 := piTensorRevEquiv (fun a => (x a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK x a) (revPi fun a => GL (Fin (x a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (x a).1) fun a => (dualRev hA x a).rep)
  have T := (T1.trans T2).trans T3
  unfold jm
  rw [jhMult_congr_right _ (jacCompThetaW (fun a => (x a).1) hd hd' π), jhMult_congr_left T]
  exact GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective (thetaL fun a => (x a).1) (thetaL_surjective _) _ _

theorem jm_comp_thetaW (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL k) (hy : y = fun a => dualCl (x (Fin.rev a))) (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (y a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm y hd' π := by
  rw [← dualRev_eq hA x] at hy
  subst hy
  exact jm_comp_theta_eq_dual_reverse hA hGK x hd π

end Jacquet

theorem jmTheta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  intro k _ _ _ _ hA N V _ _ π _ _ a b hd hd'
  refine jm_comp_thetaW hA (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) _ _ ?_ hd hd' π
  funext i
  fin_cases i <;> rfl

end GlobalTheory.CompanionTheory.JmThetaInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmoothStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_product_proper_smooth : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_left | exact GlobalTheory.CompanionTheory.KunGlue.kun_left | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_left <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvertibleExistsNonzeroMinorStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_invertible_exists_nonzero_minor : ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
    L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse | exact GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse | (intros; apply GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConstancyTwistedTranslateStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_constancy_twisted_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)), IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧ HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.TwFibre.twisted_fibre_isLocallyConstant_hasCompactSupport | exact GlobalTheory.CompanionTheory.BZPhiPG.TwFibre.twisted_fibre_isLocallyConstant_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.TwFibre.twisted_fibre_isLocallyConstant_hasCompactSupport <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_finite_place_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (v : Pl F) (u : J → E) (δ : (Fv F v ⊗[F] E)ˣ) (z : J → Fv F v ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : Fv F v) ⊗ₜ[F] u f) * δ.1) → (∀ f, absFin F v (z f) ≤ c) →
    GlobalTheory.Doubling.absEv F E v δ * locFin σ v u ≤ c ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le | exact GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_infinite_place_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w) (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) → (∀ f, ‖infEmb e (z f)‖₊ ≤ c) →
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | exact GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSequenceNormBoundsStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_sequence_norm_bounds : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → 2 ≤ qOf π → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) ∧ ∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.Normz.norm_z_bounds | exact GlobalTheory.CompanionTheory.LTPer.Tilt.Normz.norm_z_bounds | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.Normz.norm_z_bounds <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTeichmullerSequenceCompatibilityStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_teichmuller_sequence_compatibility : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (z : ℕ → Om l) (f : ℕ), 0 < f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) → (∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖) →
    ∀ (u : ℕ → Tl l), (∀ n, u (n + 1) ^ l ^ f = u n) → (∀ n, ‖sh (u n) - omC (z n)‖ ≤ ‖oc K π‖) →
    ∀ (r₀ : ↥(OL K) →+* Tl l), (∀ c, r₀ c ^ l ^ f = r₀ c) → (∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖) →
    (∀ n, u n ≠ 0) → ∀ (g : GQ l) (c : ℕ → ↥(OL K)),
    (∀ n, HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * z n ^ k) (g (z n))) → ∀ n D : ℕ,
    u n ^ D ∣ actT g (u n) - ∑ i ∈ Finset.range D, r₀ (c i) * u n ^ i := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv | exact GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv <;> assumption)
end
end

