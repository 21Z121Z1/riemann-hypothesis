import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0174
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ModelAtBare
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem exists_algExp {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) {n : ℕ} (z : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1))
    (hz : ∀ l, IsAlgebraic ℚ (z l)) (hx : evK YS v₀ hρ i j b x = ∑ l, z l • evW YS v₀ j (g l).val) :
    ∃ (m : ℕ) (a : Fin m → NX.KB S i b) (g' : Fin m → NX.FmK S ((j : ℕ) + 1)),
      x = ∑ k, a k ⊗ₜ[S.Ks] g' k ∧ ∀ k, IsAlgebraic ℚ (ρ.e i b (a k)) := by
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  have hB : ∀ k, B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) := fun k =>
    Algebra.TensorProduct.basis_apply _ _
  have hxe : x = ∑ k, B.equivFun x k ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1)) := by
    conv_lhs => rw [← B.sum_equivFun x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB]
    change (B.equivFun x k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1)) = _
    rw [smul_eq_mul, mul_one]
  refine ⟨m, B.equivFun x, fun k => bK k, hxe, ?_⟩

  have h1 : evK YS v₀ hρ i j b x = ∑ k, ρ.e i b (B.equivFun x k) • φ k := by
    conv_lhs => rw [hxe]
    refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (evK_tmul YS v₀ hρ i j b _ _).trans (congrArg _ (congrArg (evW YS v₀ j) (hbK k)))

  let emb : S.Ks →+* ℂ := D.what₂.embLL.comp (algebraMap S.Ks D.what₂.LL)
  let c : Fin n → Fin m → S.Ks := fun l => bK.equivFun (g l)
  have h2 : ∀ l, evW YS v₀ j (g l).val = ∑ k, emb (c l k) • φ k := fun l => by
    have e : (g l).val = ∑ k, algebraMap S.Ks D.what₂.LL (c l k) • bb k := by
      conv_lhs => rw [← bK.sum_equivFun (g l)]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, hbK, algebraMap_smul]
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evW_smul]
    rfl
  have h3 : ∑ l, z l • evW YS v₀ j (g l).val = ∑ k, (∑ l, z l * emb (c l k)) • φ k := by
    simp_rw [h2, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h4 : ∀ k, ρ.e i b (B.equivFun x k) = ∑ l, z l * emb (c l k) := by
    have h5 : ∑ k, (ρ.e i b (B.equivFun x k) - ∑ l, z l * emb (c l k)) • φ k = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hx, h3, sub_self]
    intro k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hφ _ h5 k)
  intro k
  rw [h4 k]
  have hemb : ∀ y : S.Ks, IsAlgebraic ℚ (emb y) := fun y =>
    (Algebra.IsAlgebraic.isAlgebraic y).algHom emb.toRatAlgHom
  have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
  refine (hmem _).1 ?_
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · exact (hmem _).2 (hz l)
  · exact (hmem _).2 (hemb _)

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

def SerAlg : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
      ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
        ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem expAlg_of_serAlg (hS : SerAlg) : ExpAlg := by
  unfold ExpAlg SerAlg AtTw AtPts at *
  refine hS.imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf => ?_⟩
  obtain ⟨n, z, g, hz, hsum⟩ := hx0 x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hp.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  refine exists_algExp p.nexp p.v₀ hρ _ j _ hU hW (Z.vec j) hK _ z g hz ?_
  rw [← hsum, ← hf]
  exact (smul_inv_smul₀ hN.1 _).symm

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

def SerRef : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∃ ν₀ : ℂ, IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν₀ ∧ RatBase (rdAt p w j hρ ν₀) ∧
    ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
      P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
        ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
          ν₀ • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val

theorem isAlgebraic_of_pow_eq_one {ζ : ℂ} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : IsAlgebraic ℚ ζ :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1, by simp [h]⟩

theorem serAlg_of_ref (hR : SerRef) (hS : ScaleRoot) : SerAlg := by
  unfold SerAlg SerRef ScaleRoot AtTw AtPts at *
  refine (Formalism.MainNotions.Closed.and hR hS).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨ν₀, hN₀, hR₀, hexp⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0
  obtain ⟨n, z, g, hz, hsum⟩ := hexp s h P hd hP
  by_cases hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, ?_⟩
    rw [hθ, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]
  · obtain ⟨m, hm0, hpow⟩ := a2 hm w hw j ρ ρ hρ hρ ν₀ ν hpin hpin ⟨rfl, rfl, rfl, rfl, rfl⟩ hN₀ hN hR₀ hR0 s h P hd hP hθ
    have h0 : ν₀ ≠ 0 := hN₀.1
    have hζ : (ν / ν₀) ^ m = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero _ h0)]
    refine ⟨n, fun k => ν / ν₀ * z k, g, fun k => ?_, ?_⟩
    · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
      exact (hmem _).1 (mul_mem ((hmem _).2 (isAlgebraic_of_pow_eq_one hm0 hζ)) ((hmem _).2 (hz k)))
    · conv_lhs => rw [← div_mul_cancel₀ ν h0]
      rw [mul_smul, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem continuous_mapLoc (w : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))

omit [IsCMField E] in
theorem entry_mem_of_mem_KGL {w : Pl E} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    g.val i j ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  obtain ⟨k, rfl⟩ := hg
  exact (k.val i j).2

omit [IsCMField E] in

theorem isCompact_box (D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E))) (hD : ∀ w, IsCompact (D w))
    (hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w n) :
    IsCompact {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
  let Q : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) '' D w
  let Q' : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => (g⁻¹).val i j) '' D w
  have hQ : ∀ i j w, IsCompact (Q i j w) := fun i j w =>
    (hD w).image (Units.continuous_val.matrix_elem i j)
  have hQ' : ∀ i j w, IsCompact (Q' i j w) := fun i j w =>
    (hD w).image (Units.continuous_coe_inv.matrix_elem i j)
  have hQK : ∀ i j, ∀ᶠ w in cofinite, Q i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL (hw hg) i j
  have hQK' : ∀ i j, ∀ᶠ w in cofinite, Q' i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL w n).inv_mem (hw hg)) i j
  let P : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q i j w}
  let P' : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q' i j w}
  have hP : IsCompact P := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q i j) (hQ i j) (hQK i j)
  have hP' : IsCompact P' := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q' i j) (hQ' i j) (hQK' i j)
  have hC : IsClosed {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun w => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact (hD w).isClosed.preimage (continuous_mapLoc w)
  refine IsCompact.of_isClosed_subset (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hP.prod (hP'.image MulOpposite.continuous_op))) hC ?_
  intro g hg
  refine ⟨fun i _ j _ w => ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, rfl⟩, ⟨(g⁻¹ : GL (Fin n) (Af E)).val, fun i _ j _ w => ?_, rfl⟩⟩
  refine ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, ?_⟩
  show ((GeneralLinearGroup.map (pLoc E w) g)⁻¹ : GL (Fin n) (w.adicCompletion E)).val i j = _
  rw [← map_inv]
  rfl

end GlobalTheory.BCT.LocCpt

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries' {K : Type} [Field K] (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_or_conj_mem {S : Set (Pl E)} (hS : IsSection S) (w : Pl E) :
    w ∈ S ∨ conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S := by
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases hw : IsSplitAt w
  · rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
    · exact Or.inl huS
    · exact Or.inr huS
  · left
    by_contra hwS
    exact hw ⟨u, fun h => hwS (h ▸ huS), hu⟩

theorem cLoc_eq_invT (x : UA E n) (w : Pl E) :
    cLoc w x = invT n _ (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)) := by
  set Y := GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)
  have h : (Y.val)ᵀ * (cLoc w x).val = 1 := GlobalTheory.SplitPts.comp_eq x w
  apply Units.ext
  show (cLoc w x).val = ((Y⁻¹).val)ᵀ
  calc (cLoc w x).val = ((Y⁻¹).val)ᵀ * ((Y.val)ᵀ * (cLoc w x).val) := by
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
    _ = ((Y⁻¹).val)ᵀ := by rw [h, Matrix.mul_one]

end GlobalTheory.BCT.LocCpt

open GlobalTheory.BCT.LocCpt in

theorem GlobalTheory.BCT.LocCpt.loc_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E),
    IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) →
    IsCompact {x : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  intro E _ _ _ hU n S hS C hC hCK
  set c := GlobalTheory.SplitPts.conjE E
  let φ : ∀ w : Pl E, GL (Fin n) ((conjSrc c w).adicCompletion E) → GL (Fin n) (w.adicCompletion E) :=
    fun w g => invT n _ (GeneralLinearGroup.map (conjLoc c w) g)
  have hφ : ∀ w, Continuous (φ w) := fun w => (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec c w).1))
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w ∈ S then Subtype.val '' C w else φ w '' (Subtype.val '' C (conjSrc c w))
  have hD : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ S
    · simp only [D, if_pos hw]; exact (hC w).image continuous_subtype_val
    · simp only [D, if_neg hw]; exact ((hC _).image continuous_subtype_val).image (hφ w)
  have hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w n := by
    have h1 : ∀ᶠ w in cofinite, C (conjSrc c w) = KL n (conjSrc c w) :=
      (conjSrc_injective c).tendsto_cofinite.eventually hCK
    filter_upwards [hCK, h1] with w hw hw'
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS, hw]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hk
    · simp only [D, if_neg hwS, hw']
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hk' : (k : GL (Fin n) _) ∈ GlobalTheory.LFun.KGL (conjSrc c w) n := Subgroup.mem_subgroupOf.1 hk
      have hO : ∀ y, y ∈ ((conjSrc c w).adicCompletionIntegers E : Set _) →
          conjLoc c w y ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := fun y hy => by
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec c w).2.2 y]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
      apply mem_GLint_of_entries'
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL _ n).inv_mem hk') b a)
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL hk' b a)
  have hB := isCompact_box D hD hDK

  have hmem : ∀ (x : finU E n) (w : Pl E), toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w ↔
      cLoc w (x : UA E n) ∈ Subtype.val '' C w := by
    intro x w
    have hx := GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (x : UA E n)
    rw [toSub, dif_pos hx]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨k, hk, e⟩
      have : k = ⟨_, hx⟩ := Subtype.ext e
      rwa [← this]
  have hclosed : IsClosed {x : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
    simp only [hmem, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact ((hC w).image continuous_subtype_val).isClosed.preimage
      ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)

  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine IsCompact.of_isClosed_subset (hι.isCompact_preimage (hB.image GlobalTheory.DefU.LocAdm.continuous_finGL)) hclosed ?_
  intro x hx
  refine ⟨GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n), fun w => ?_, ?_⟩
  · have e : ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n)) =
        cLoc u (x : UA E n) := fun u => Units.ext rfl
    rw [e]
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS]
      exact (hmem x w).1 (hx w hwS)
    · simp only [D, if_neg hwS]
      have hw' := (mem_or_conj_mem hS w).resolve_left hwS
      refine ⟨cLoc (conjSrc c w) (x : UA E n), (hmem x _).1 (hx _ hw'), ?_⟩
      exact (cLoc_eq_invT (x : UA E n) w).symm
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportComp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isTransp_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ γ γ' k k₁ k₂ a a' h₁ h₂
  obtain ⟨m₁, f₁, l₁⟩ := h₁
  obtain ⟨m₂, f₂, l₂⟩ := h₂
  have hP := (h.laws v).p
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left 1 _, i.isLt⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1)
    (GlobalTheory.Proof.ModelAtPrimeToLevel.one_le_rank hP hj) hP.pins.2.1.2
  have hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k₂) (a * a') :=
    { psi := m₁.psi.trans m₂.psi
      p0 := m₁.p0.trans m₂.p0
      xi := m₁.xi.trans m₂.xi
      iso := fun u w => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, m₂.iso, m₁.iso]
      lat := fun w => by
        rw [m₁.lat, m₂.lat, Units.val_mul, Matrix.mulVec_mulVec] }
  refine ⟨hm, fun x hx => ?_, fun w => ?_⟩
  · obtain ⟨hy₁, t₁, b₁⟩ := f₁ x hx
    obtain ⟨hy₂, t₂, b₂⟩ := f₂ _ hy₁
    have ef : castFrame hm.psi (lact (a * a') x) =
        castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) := by
      funext τ
      simp only [castFrame, lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
      rw [mul_assoc]
      rfl
    set Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)
    set c := (r.used v).full.Q.c
    set y₀ := (uAt r v i).un k ⟨x, hx⟩
    set y₁ := (uAt r v i).un k₁ ⟨castFrame m₁.psi (lact a' x), hy₁⟩
    have e1 := hL.mul γ' γ _ y₀ _ _ (mvPt_spec hL.total γ' y₀) (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e2 := hL.func (γ' * γ) _ y₀ _ _ (mvPt_spec hL.total (γ' * γ) y₀) e1
    have e3 : mvLev Xo c γ (mvLev Xo c γ' y₀) = mvLev Xo c (γ' * γ) y₀ :=
      ((GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).1 _ _ e2
        (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).2.1)
    have e4 := hL.bor γ _ t₁ y₁ _ (mvLev Xo c γ' y₀) _ b₁ (mvPt_spec hL.total γ y₁)
      (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e5 := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ _ _ _ _ _ _).2.1 t₂ t₁ _ _ _ b₂ e4
    have key : ∀ (z : Frame ((uAt r v i).X k₂).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k₂).dom),
        z = castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) →
        FrBor (t₂ * t₁) ((uAt r v i).un k₂ ⟨z, hz⟩) (mvLev Xo c (γ' * γ) y₀) := by
      rintro z hz rfl
      rw [← e3]
      exact e5
    exact ⟨ef ▸ hy₂, t₂ * t₁, key _ _ ef⟩
  · obtain ⟨hw₁, q₁⟩ := l₁ w
    obtain ⟨hw₂, q₂⟩ := l₂ ⟨_, hw₁⟩
    have e : ((a * a' : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E) =
        (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec
          ((a' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E)) := by
      rw [Units.val_mul, Matrix.mulVec_mulVec]
    have hs : ∀ z, (γ' * γ).symm z = γ.symm (γ'.symm z) := fun z =>
      (γ' * γ).injective (by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply])
    rw [e]
    refine ⟨hw₂, q₂.trans ?_⟩
    refine congrArg (ψ k₂) ?_
    refine (congrArg γ.symm ((congrArg (ψ k₁).symm q₁).trans ((ψ k₁).symm_apply_apply _))).trans ?_
    exact (hs _).symm

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def MovesAt (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom) : Prop :=
  ∃ (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _),
    FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩) (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩))

def ReadsInv (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) : Prop :=
  ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
    ∃ hw : Matrix.mulVec (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (w : Fin D.R.r → D.host.E) ∈
        lattice₂ D ((uAt r v i).X k').Λ,
      Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k').Λ))) ⟨_, hw⟩ =
        ψ k' (γ.symm ((ψ k).symm (Submodule.Quotient.mk w)))

theorem isTransp_of_movesAt {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} {i : Fin D.R.m}
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k}
    {γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l}
    {k k' : (uAt r v i).Comp} {a : GL (Fin D.R.r) D.host.E}
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (h₁ : ∀ x hx, MovesAt p r i v γ k k' a hm x hx) (h₂ : ReadsInv p r i v ψ γ k k' a) :
    IsTransp p r i v ψ γ k k' a :=
  ⟨hm, h₁, h₂⟩

end GlobalTheory.ShareOn

end
end

