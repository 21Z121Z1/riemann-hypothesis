import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleFiniteTypeFrameOfCuspMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.AdmOfHom

theorem isAdmissible_finRep : GlobalTheory.Published.HarishChandraFinite → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S') (Φ : GfC V ≃ₜ* GfC V') (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P' : LevelP L.Pg L.r ℂ) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), L.s = 0 → L.Q = ∅ → killed ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (eqSet V β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) ≠ ⊥ → (homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M) ≠ ⊥ ∨ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) ((finRep M').comp Φ.toMulEquiv.toMonoidHom) (allMaps θ M') ≠ ⊥) → GlobalTheory.PRep.IsAdmissible ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) := by
  intro hP D θ hθ V V' S S' M M' Φ β L G _ _ eG c P' n P π hs hQ hk hhom
  set σ : Representation ℂ (GfC V) π.S := (GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom with hσdef
  have hirr : ∀ U : Submodule ℂ π.S, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤ := fun U hU =>
    GlobalTheory.OccRowVec.finRep_irr π U fun g x hx => by
      have := hU (GlobalTheory.KapIsot.eqv P g) x hx
      simpa [σ] using this
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have ho := GlobalTheory.PartDims.isOpen_stab hs hQ hy
  haveI := GlobalTheory.PartDims.isTopologicalGroup_GA V
  rcases hhom with h | h
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact GlobalTheory.KapIsot.isAdmissible_of hirr hy0 ho hf hf0
      (fun K hK => GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine GlobalTheory.KapIsot.isAdmissible_of hirr hy0 ho hf hf0 (fun K hK => ?_)
    have hK' : IsOpen ((K.map Φ.toMulEquiv.toMonoidHom : Subgroup (GfC V')) : Set (GfC V')) := by
      rw [Subgroup.coe_map]
      exact Φ.toHomeomorph.isOpenMap _ hK
    haveI := GlobalTheory.CuspDec.finiteDimensional_fixed (M := M') hP hθ _ hK'
    refine Submodule.finiteDimensional_of_le (S₂ := allMaps θ M' ⊓ GlobalTheory.PRep.fixed (finRep M') (K.map Φ.toMulEquiv.toMonoidHom))
      fun x hx => ⟨hx.1, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => ?_⟩
    obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.1 hk
    exact GlobalTheory.CuspDec.mem_fixed.1 hx.2 k0 hk0

end GlobalTheory.AdmOfHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
section
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

variable {g : ℕ} [Fact g.Prime]

theorem mem_unipRadical_twoBlocks_iff {d a : ℕ} (had : a ≤ d) (x : Gn g d) :
    x ∈ unipRadical (ZMod g) (twoBlocks d a) ↔
      (InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = 1 ∧ br a (d - a) (x : Mt g d) = 1) := by
  rw [mem_unipRadical]
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · have := h i j (by simp [twoBlocks]; split_ifs <;> omega)
      have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    · funext i j
      have := h ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [twoBlocks, i.2, j.2])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · funext i j
      have := h ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ (by simp [twoBlocks])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show a + (i : ℕ) < d ∧ a + (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
  · rintro ⟨hP, htl, hbr⟩ i j hij
    rw [Matrix.sub_apply, sub_eq_zero]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have := congrFun (congrFun htl ⟨i, hi⟩) ⟨j, hj⟩
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d from ⟨i.2, j.2⟩)] at this
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · exfalso
      simp [twoBlocks, hi, hj] at hij
    · have hne : i ≠ j := fun e => by rw [e] at hi; exact hi hj
      rw [hP i j hj (not_lt.1 hi), Matrix.one_apply_ne hne]
    · have := congrFun (congrFun hbr ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN] at this
      rw [dif_pos (show a + ((i : ℕ) - a) < d ∧ a + ((j : ℕ) - a) < d by omega)] at this
      have ei : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
      have ej : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
      rw [ei, ej] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.ext_iff]
      split_ifs with h1 h2 h2 <;> first | rfl | omega

open scoped Classical in

theorem res_one_one_eq {d a : ℕ} (had : a ≤ d) (χ : Gn g d → ℂ) :
    res a (d - a) χ 1 1 =
      ((g : ℂ) ^ (a * (d - a)))⁻¹ * ∑ u : unipRadical (ZMod g) (twoBlocks d a), χ u := by
  unfold res
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_subtype _ (fun x => ?_) χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Units.val_one]
  exact (mem_unipRadical_twoBlocks_iff had x).symm

open scoped Classical in

theorem res_character_eq_zero_iff {d a : ℕ} (had : a ≤ d) (V : FDRep ℂ (Gn g d)) :
    res a (d - a) (fun x => V.character x) 1 1 = 0 ↔
      ∀ v : V, (∀ u ∈ unipRadical (ZMod g) (twoBlocks d a), V.ρ u v = v) → v = 0 := by
  rw [res_one_one_eq had, mul_eq_zero]
  have hg : ((g : ℂ) ^ (a * (d - a)))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero))
  simp only [hg, false_or]
  have h := GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff
    (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype)
  have e : ∀ u : unipRadical (ZMod g) (twoBlocks d a),
      Representation.character (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype) u = V.character u := fun u => rfl
  simp only [e] at h
  rw [h]
  constructor
  · intro H v hv
    exact H v fun u => hv u u.2
  · intro H v hv
    exact H v fun u hu => hv ⟨u, hu⟩

def cb (d a : ℕ) : Fin d → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1

theorem val_cb (d a : ℕ) (i : Fin d) : ((cb d a i : Fin 2) : ℕ) = twoBlocks d a i := by
  simp only [cb, twoBlocks]
  split_ifs <;> rfl

theorem mem_unipRadical_of_mem_unip {d a : ℕ} {u : Gn g d} (hu : u ∈ unip (ZMod g) (cb d a)) :
    u ∈ unipRadical (ZMod g) (twoBlocks d a) := by
  obtain ⟨⟨hA, -⟩, hD⟩ := hu
  rw [mem_unipRadical]
  intro i j hij
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases e : cb d a i = cb d a j
  · rw [hD i j e]
    simp
  · have hlt : cb d a j < cb d a i := by
      rw [Fin.lt_iff_val_lt_val, val_cb, val_cb]
      have e' : twoBlocks d a i ≠ twoBlocks d a j := fun h => e (Fin.ext (by rw [val_cb, val_cb, h]))
      omega
    have hne : i ≠ j := fun h => e (by rw [h])
    rw [hA i j hlt, if_neg hne, sub_zero]

theorem glEquiv_mem_unip {d a s : ℕ} (b : Fin d → Fin s) (z : Fin s) (hz : ∀ i, z ≤ b i) (σ : Fin d ≃ Fin d)
    (hσ : ∀ k : Fin d, (k : ℕ) < a ↔ b (σ k) = z) {u : Gn g d} (hu : u ∈ unipRadical (ZMod g) (twoBlocks d a)) :
    glEquiv (ZMod g) σ u ∈ unip (ZMod g) b := by
  have htb : ∀ i, twoBlocks d a (σ.symm i) = if b i = z then 0 else 1 := by
    intro i
    have h := hσ (σ.symm i)
    rw [Equiv.apply_symm_apply] at h
    simp only [twoBlocks]
    by_cases hb : b i = z
    · simp [hb, h.2 hb]
    · simp [hb, mt h.1 hb]
  have hent : ∀ w : Gn g d, w ∈ unipRadical (ZMod g) (twoBlocks d a) → ∀ i j, (b j = z ∨ b i ≠ z) →
      ((glEquiv (ZMod g) σ w : Gn g d) : Mt g d) i j = if i = j then 1 else 0 := by
    intro w hw i j hij
    rw [Formalism.L2.PT.coe_glEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
    have h0 := (mem_unipRadical.1 hw) (σ.symm i) (σ.symm j) (by
      rw [htb, htb]
      rcases hij with h | h
      · by_cases h' : b j = z <;> simp [h, h']
      · by_cases h' : b j = z <;> simp [h, h'])
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at h0
    rw [h0]
    simp [σ.symm.injective.eq_iff]
  have hlt : ∀ i j, b j < b i → b i ≠ z := fun i j h e => by
    have := hz j
    rw [e] at h
    exact absurd (lt_of_le_of_lt this h) (lt_irrefl _)
  have hne : ∀ i j : Fin d, b j < b i → i ≠ j := fun i j h e => by rw [e] at h; exact lt_irrefl _ h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j h
    rw [hent u hu i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [← map_inv, hent u⁻¹ (inv_mem hu) i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [hent u hu i j (by by_cases e : b i = z <;> simp_all)]

theorem exists_perm_first {d s : ℕ} (b : Fin d → Fin s) (z : Fin s) :
    ∃ σ : Fin d ≃ Fin d, ∀ k : Fin d, (k : ℕ) < Fintype.card {i // b i = z} ↔ b (σ k) = z := by
  classical
  set a := Fintype.card {i // b i = z} with ha
  have had : a ≤ d := (Fintype.card_subtype_le _).trans (by simp)
  have hca : Fintype.card {k : Fin d // (k : ℕ) < a} = a := by
    rw [Fintype.card_congr (show {k : Fin d // (k : ℕ) < a} ≃ Fin a from
      { toFun := fun k => ⟨k.1, k.2⟩
        invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 had⟩, i.2⟩
        left_inv := fun k => rfl
        right_inv := fun i => rfl }), Fintype.card_fin]
  let e1 : {k : Fin d // (k : ℕ) < a} ≃ {i // b i = z} := Fintype.equivOfCardEq (by rw [hca])
  let e2 : {k : Fin d // ¬ (k : ℕ) < a} ≃ {i // ¬ b i = z} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hca])
  refine ⟨((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))), fun k => ?_⟩
  by_cases hk : (k : ℕ) < a
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e1 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun _ => (e1 ⟨k, hk⟩).2, fun _ => hk⟩
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e2 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun h => absurd h hk, fun h => absurd h (e2 ⟨k, hk⟩).2⟩

end GlobalTheory.CuspCharRep

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

theorem isCusp_character_iff_isCuspidal : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))),
    1 ≤ d → CategoryTheory.Simple V →
      (GlobalTheory.GLq.IsCusp (fun x => V.character x) ↔ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V) := by
  intro g _ d V hd hV
  unfold GlobalTheory.GLq.IsCusp
  constructor
  · rintro ⟨-, -, hres⟩ s b hb hs v hv
    let z : Fin s := ⟨0, by omega⟩
    have hz : ∀ i, z ≤ b i := fun i => show (0 : ℕ) ≤ (b i : ℕ) from Nat.zero_le _
    obtain ⟨σ, hσ⟩ := exists_perm_first b z
    have ha0 : 0 < Fintype.card {i // b i = z} :=
      Fintype.card_pos_iff.2 ⟨⟨(hb z).choose, (hb z).choose_spec⟩⟩
    have had : Fintype.card {i // b i = z} < d := by
      obtain ⟨j, hj⟩ := hb ⟨1, by omega⟩
      have h := Fintype.card_subtype_lt (p := fun i => b i = z) (x := j)
        (by rw [hj]; simp [Fin.ext_iff, z])
      simpa using h
    have hw := (res_character_eq_zero_iff had.le V).1 (hres _ ha0 had)
    let P := GlobalTheory.SerOSys.TranspLabel.permGL (K := ZMod g) σ
    have key : V.ρ P⁻¹ v = 0 := hw _ fun u hu => by
      have h1 := hv _ (glEquiv_mem_unip b z hz σ hσ hu)
      rw [GlobalTheory.SerOSys.TranspLabel.glEquiv_perm] at h1
      calc V.ρ u (V.ρ P⁻¹ v) = V.ρ (P⁻¹ * (P * u * P⁻¹)) v := by
            rw [show P⁻¹ * (P * u * P⁻¹) = u * P⁻¹ by group, map_mul, Module.End.mul_apply]
        _ = V.ρ P⁻¹ v := by rw [map_mul, Module.End.mul_apply, h1]
    calc v = V.ρ (P * P⁻¹) v := by rw [mul_inv_cancel, map_one, Module.End.one_apply]
      _ = 0 := by rw [map_mul, Module.End.mul_apply, key, map_zero]
  · intro hc
    refine ⟨by omega, ⟨V, hV, fun _ => rfl⟩, fun a ha had => ?_⟩
    rw [res_character_eq_zero_iff had.le V]
    intro v hv
    refine hc 2 (cb d a) ?_ le_rfl v fun u hu => hv u (mem_unipRadical_of_mem_unip hu)
    intro k
    fin_cases k
    · exact ⟨⟨0, by omega⟩, by simp [cb, ha]⟩
    · exact ⟨⟨a, had⟩, by simp [cb]⟩

end GlobalTheory.CuspCharRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletionStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isCompact_parahoric_GL_completion : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  first | exact @GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ | exact GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ | (intros; apply GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotNeBotRead
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem.R3

namespace GlobalTheory.KapIsotRead

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isot_ne_bot_read : GlobalTheory.Published.HarishChandraFinite → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.L2.DIV.GoodStable A3.A.X → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥ := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPin hH hME hGS hgen σ i
  have hL := Y.tied.lift
  obtain ⟨w, hw, hw0⟩ := GlobalTheory.KapIsot.exists_mem_isotL hP R.toRealDat F.lv2 hH.ok.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hPin.char hH.aux.ex).1 hME hGS hgen Y.hF Y.PY i (Y.PW i) Y.stdPsi.1 (Y.stdPsi.2 i) (principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ))) (principalLevelFrame.rowRepR_occ _ _)
  intro hbot
  let L := RecTie.toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj
  let lw : L.AmbW i := (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i) w
  have hgood : lw ∈ L.Wc i := Submodule.mem_map_of_mem hw.1
  let y : D.what₂.Mj ((i : ℕ) + 1) := (Y.IL.jMj i).symm ⟨lw, hgood⟩
  have hjy : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) = lw := by
    simp only [y, LinearEquiv.apply_symm_apply]
  have hmem : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) ∈ Y.IL.prtW i (D.what₂.ft σ) := by
    rw [hjy, Y.prtWE]
    exact ⟨w, hw, rfl⟩
  have hy0 : y ∈ D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) := (hL.isot i _ y).2 hmem
  rw [hbot, Submodule.mem_bot] at hy0
  apply hw0
  have h1 : lw = 0 := by rw [← hjy, hy0, map_zero]; rfl
  exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i).injective (h1.trans (map_zero _).symm)

end GlobalTheory.KapIsotRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumEqOfFramesInnerConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.FrameIsot

variable {H S X : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]

theorem iSup_le_of_intertwine (σ₁ σ₂ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (T : S →ₗ[ℂ] S) (hT : Function.Surjective T) (hc : ∀ g s, σ₁ g (T s) = T (σ₂ g s)) :
    (⨆ f ∈ homInto σ₁ ρ C, LinearMap.range f) ≤ ⨆ f ∈ homInto σ₂ ρ C, LinearMap.range f := by
  refine iSup₂_le fun f hf => ?_
  have hm : f ∘ₗ T ∈ homInto σ₂ ρ C := by
    refine ⟨fun s => hf.1 (T s), fun g s => ?_⟩
    show f (T (σ₂ g s)) = ρ g (f (T s))
    rw [← hc]; exact hf.2 g (T s)
  have hr : LinearMap.range (f ∘ₗ T) = LinearMap.range f := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hT, Submodule.map_top]
  exact hr ▸ le_iSup₂_of_le (f ∘ₗ T) hm le_rfl

end GlobalTheory.FrameIsot

open GlobalTheory.FrameIsot in
theorem GlobalTheory.FrameIsot.iSup_homInto_frame_conj : ∀ {D : D7} (Y W : HSp D) {n : ℕ} (PY : principalLevelFrame.RowPsi Y n) (PW : principalLevelFrame.RowPsi W n) (Φ : GfC Y ≃ₜ* GfC W) (h : Formalism.AUTREP.GAf D.host.E n), (∀ κ, ((Φ ⟨PY.ψ κ, PY.into κ⟩ : GfC W) : GA D W) = PW.ψ (h * κ * h⁻¹)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC W) X) (C : Submodule ℂ X) (π : Formalism.L2.NG.FinTyp D.host.E n), (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) (ρ.comp Φ.toMulEquiv.toMonoidHom) C, LinearMap.range f) = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PW).symm.toMonoidHom) ρ C, LinearMap.range f := by
  intro D Y W n PY PW Φ h hΦ X _ _ ρ C π
  rw [GlobalTheory.PartDims.homInto_comp]
  set eY := GlobalTheory.KapIsot.eqv PY
  set eW := GlobalTheory.KapIsot.eqv PW
  have key : ∀ κ', eY.symm (Φ.toMulEquiv.symm (eW κ')) = h⁻¹ * κ' * h := by
    intro κ'
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    have := hΦ (h⁻¹ * κ' * h)
    rw [show h * (h⁻¹ * κ' * h) * h⁻¹ = κ' by group] at this
    exact this.symm
  have hW : ∀ κ', eW.symm (eW κ') = κ' := fun κ' => MulEquiv.symm_apply_apply _ _
  apply le_antisymm
  · refine iSup_le_of_intertwine _ _ ρ C (GlobalTheory.OccRowVec.finRep π h⁻¹) ?_ ?_
    · intro s; exact ⟨GlobalTheory.OccRowVec.finRep π h s, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]⟩
    · intro g s
      obtain ⟨κ', rfl⟩ := eW.surjective g
      show GlobalTheory.OccRowVec.finRep π (eY.symm (Φ.toMulEquiv.symm (eW κ'))) _ = GlobalTheory.OccRowVec.finRep π h⁻¹ (GlobalTheory.OccRowVec.finRep π (eW.symm (eW κ')) s)
      rw [key, hW, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
  · refine iSup_le_of_intertwine _ _ ρ C (GlobalTheory.OccRowVec.finRep π h) ?_ ?_
    · intro s; exact ⟨GlobalTheory.OccRowVec.finRep π h⁻¹ s, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    · intro g s
      obtain ⟨κ', rfl⟩ := eW.surjective g
      show GlobalTheory.OccRowVec.finRep π (eW.symm (eW κ')) _ = GlobalTheory.OccRowVec.finRep π h (GlobalTheory.OccRowVec.finRep π (eY.symm (Φ.toMulEquiv.symm (eW κ'))) s)
      rw [key, hW, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumInfGroupAlgebraKilledEqBot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.RepCount

theorem iSup_range_homInto_inf_killed_eq_bot : ∀ (H S0 X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → killed σ0 I = ⊥ → ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = ⊥ := by
  intro H S0 X _ _ _ _ _ σ0 ρ C I hirr hk
  haveI hS : IsSimpleModule (MonoidAlgebra ℂ H) σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).1 hirr
  let N : Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    ⨆ (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C), LinearMap.range (modMap f hf.2)
  have hN : N ≤ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ0.asModule := by
    refine iSup₂_le fun f hf => ?_
    rcases LinearMap.injective_or_eq_zero (modMap f hf.2) with hi | h0
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [h0, LinearMap.range_zero]; exact bot_le
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ H) N :=
    IsSemisimpleModule.of_injective _ (Submodule.inclusion_injective hN)
  have hiso : IsIsotypicOfType (MonoidAlgebra ℂ H) N σ0.asModule :=
    (IsIsotypicOfType.isotypicComponent _ _ _).of_injective _ (Submodule.inclusion_injective hN)
  obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  rw [eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  rw [Submodule.mem_bot]
  by_contra hv0
  have hvN : ρ.asModuleEquiv.symm v ∈ N := by
    have hle : (⨆ f ∈ homInto σ0 ρ C, LinearMap.range f : Submodule ℂ X) ≤
        (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup₂_le fun f hf => ?_
      rintro _ ⟨s, rfl⟩
      have hfs : ρ.asModuleEquiv.symm (f s) = modMap f hf.2 (σ0.asModuleEquiv.symm s) := by
        rw [LinearEquiv.symm_apply_eq, modMap_apply, LinearEquiv.apply_symm_apply]
      show ρ.asModuleEquiv.symm (f s) ∈ N
      rw [hfs]
      exact (le_iSup₂ (f := fun (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap f hf.2)) f hf) ⟨_, rfl⟩
    exact hle hv1
  let w : N := ⟨_, hvN⟩
  have hw : w ≠ 0 := fun h => hv0 (by
    have := congrArg (fun x : N => ρ.asModuleEquiv x.1) h
    simpa [w] using this)
  have hew : e w ≠ 0 := fun h => hw (e.map_eq_zero_iff.1 h)
  obtain ⟨i, hi⟩ : ∃ i, e w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hew (Finsupp.ext h)
  refine killed_ne_bot (LinearEquiv.refl _ σ0.asModule) hi (fun x hx => ?_) hk
  have hxw : x • w = 0 := by
    apply Subtype.ext
    show x • ρ.asModuleEquiv.symm v = 0
    apply ρ.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, mem_killed.1 hv2 x hx,
      map_zero]
  have := congrArg (fun u => e u i) hxw
  simpa [map_smul, Finsupp.smul_apply] using this

end GlobalTheory.RepCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  first | exact @GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | exact GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | (intros; apply GlobalTheory.Mem.SRe.levCols_le_triv_and_finite <;> assumption)
end

