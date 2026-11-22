import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankJointEigenspaceCoefficientFieldComplex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem jointKer_fin_finrank {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type}
    (Mg : G → Matrix ι ι K) (s : Finset G) :
    Module.finrank K ↥(⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))) =
      Module.finrank C ↥(⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) := by
  classical
  let R : Matrix (↥s × ι) ι K := Matrix.of fun p b => Mg p.1.1 p.2 b
  have stack : ∀ {F : Type} [Field F] (N : G → Matrix ι ι F),
      (⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (N g))) =
        LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (p : ↥s × ι) b => N p.1.1 p.2 b)) := by
    intro F _ N
    ext c
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro h
      funext p
      have := congrFun (h p.1.1 p.1.2) p.2
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] using this
    · intro h g hg
      funext a
      have := congrFun h (⟨g, hg⟩, a)
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] using this
  have rn : ∀ {F : Type} [Field F] (N : Matrix (↥s × ι) ι F),
      N.rank + Module.finrank F (LinearMap.ker N.mulVecLin) = Fintype.card ι := by
    intro F _ N
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    exact this
  have h1 := rn R
  have h2 := rn (R.map φ)
  rw [GlobalTheory.Core.Rk.rank_map_field] at h2
  rw [stack Mg, stack (fun g => (Mg g).map φ)]
  have e : (Matrix.of fun (p : ↥s × ι) b => ((Mg p.1.1).map φ) p.2 b) = R.map φ := by
    ext p b
    rfl
  rw [e]
  change Module.finrank K ↥(LinearMap.ker (Matrix.mulVecLin R)) = _
  omega

theorem jointKer_finrank {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type}
    (Mg : G → Matrix ι ι K) :
    Module.finrank K ↥(⨅ g, LinearMap.ker (Matrix.mulVecLin (Mg g))) =
      Module.finrank C ↥(⨅ g, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) := by
  classical
  let kK : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  let kC : Finset G → Submodule C (ι → C) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))
  have heq : ∀ s, Module.finrank K (kK s) = Module.finrank C (kC s) := fun s => jointKer_fin_finrank φ Mg s
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kK s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kK s) ≤ Module.finrank K (kK s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hminC : ∀ s' : Finset G, Module.finrank C (kC s) ≤ Module.finrank C (kC s') := fun s' => by
    rw [← heq, ← heq]; exact hmin s'
  have hK : (⨅ g, LinearMap.ker (Matrix.mulVecLin (Mg g))) = kK s := by
    apply le_antisymm
    · exact le_iInf₂ fun g _ => iInf_le _ g
    · refine le_iInf fun g => ?_
      have hins : kK (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kK s := by
        simp only [kK, Finset.iInf_insert]
      have hle : kK (insert g s) ≤ kK s := by rw [hins]; exact inf_le_right
      have h := Submodule.eq_of_le_of_finrank_le hle (hmin _)
      rw [← h, hins]
      exact inf_le_left
  have hC : (⨅ g, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) = kC s := by
    apply le_antisymm
    · exact le_iInf₂ fun g _ => iInf_le _ g
    · refine le_iInf fun g => ?_
      have hins : kC (insert g s) = LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ)) ⊓ kC s := by
        simp only [kC, Finset.iInf_insert]
      have hle : kC (insert g s) ≤ kC s := by rw [hins]; exact inf_le_right
      have h := Submodule.eq_of_le_of_finrank_le hle (hminC _)
      rw [← h, hins]
      exact inf_le_left
  rw [hK, hC]
  exact heq s

end GlobalTheory.PtLocalEig

namespace GlobalTheory.PtLocalEig

theorem eig_dim : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := by
  intro D M B j w μ h1 h2 hμ φ hφ κ E hex hadd hE
  subst hμ
  classical
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  have hbV : ∀ a, bV a = B.iV j w (b a) := fun a => by simp [bV]
  have rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r
  have rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r
  let A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL :=
    fun v k => LinearMap.toMatrix b b (B.hL j w v k)
  let G := {p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}
  let Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w)) :=
    fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1
  set Mw := M (D.what₂.muTw w) j h1 h2 with hMw

  have hV : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k) c,
      B.hK j w v k (bV.equivFun.symm c) = κ v k • bV.equivFun.symm c ↔ Matrix.mulVec (Mg ⟨(v, k), hvk⟩) c = 0 := by
    intro v k hvk c
    have hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w) := by
      ext r c'
      rw [LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]
      simp only [A, LinearMap.toMatrix_apply]
    have hr := LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)
    rw [hmat] at hr
    have hc : ⇑(bV.repr (bV.equivFun.symm c)) = c := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hc] at hr
    rw [← bV.equivFun.injective.eq_iff, map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr]
    simp only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hPV : (⨅ (v : PlE D.host) (k : ℕ) (_ : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k),
      Module.End.eigenspace (B.hK j w v k) (κ v k)).map (bV.equivFun : B.V j w →ₗ[FractionRing (B.Oc j w)] _) =
      ⨅ g : G, LinearMap.ker (Matrix.mulVecLin (Mg g)) := by
    ext c
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro h ⟨⟨v, k⟩, hvk⟩
      exact (hV v k hvk c).1 (h v k hvk)
    · intro h v k hvk
      exact (hV v k hvk c).2 (h ⟨⟨v, k⟩, hvk⟩)

  have hCk : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k) (y : D.what₂.Mt (D.what₂.muTw w) j),
      (∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ →
        Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y) = φ (κ v k) • Mw.real y) ↔
      Matrix.mulVec ((Mg ⟨(v, k), hvk⟩).map φ) (bC.equivFun y) = 0 := by
    intro v k hvk y
    obtain ⟨s0, ϖ0, hc0, hu0⟩ := hex v k hvk
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
    have hagree : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ →
        ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x) := by
      intro s ϖ hc hu
      have hadd' := hadd v k s ϖ hvk hc hu
      have htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
        have := hadd' 1 0 0
        rw [one_smul, add_zero, one_smul] at this
        simpa using this
      let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) :=
        { toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y)
          map_add' := fun y y' => by
            have := hadd' 1 (Mw.real y) (Mw.real y')
            rw [one_smul, one_smul] at this
            simp only [map_add]
            exact this
          map_smul' := fun c y => by
            have := hadd' c (Mw.real y) 0
            rw [add_zero, htN0, add_zero] at this
            simp only [map_smul, RingHom.id_apply]
            exact this }
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
        show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
        rw [e, hbC a]
        exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
      intro x
      exact LinearMap.congr_fun hLt x
    have hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.map_apply]
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c
      show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _
      rw [e, rC]
      simp only [A, LinearMap.toMatrix_apply]
    have hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1 := by
      ext r c
      simp only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hφ]
    have hvec : tC y = φ (κ v k) • y ↔ Matrix.mulVec ((Mg ⟨(v, k), hvk⟩).map φ) (bC.equivFun y) = 0 := by
      rw [hMg, Matrix.sub_mulVec, ← hmat, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero,
        Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr, ← Finsupp.coe_smul, ← map_smul]
      exact ⟨fun h => by rw [h], fun h => bC.repr.injective (DFunLike.coe_injective h)⟩
    constructor
    · intro h
      apply hvec.1
      apply Mw.real_inj
      rw [← hagree s0 ϖ0 hc0 hu0, h s0 ϖ0 hc0 hu0, map_smul]
    · intro h s ϖ hc hu
      rw [hagree s ϖ hc hu, hvec.2 h, map_smul]
  have hPC : E.map (bC.equivFun : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] _) =
      ⨅ g : G, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ)) := by
    ext d
    rw [Submodule.mem_map_equiv, hE]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro h ⟨⟨v, k⟩, hvk⟩
      have := (hCk v k hvk (bC.equivFun.symm d)).1 (fun s ϖ hc hu => h v k s ϖ hvk hc hu)
      rwa [LinearEquiv.apply_symm_apply] at this
    · intro h v k s ϖ hvk hc hu
      refine (hCk v k hvk _).2 ?_ s ϖ hc hu
      rw [LinearEquiv.apply_symm_apply]
      exact h ⟨⟨v, k⟩, hvk⟩
  rw [← LinearEquiv.finrank_map_eq bV.equivFun, hPV, ← LinearEquiv.finrank_map_eq bC.equivFun E, hPC]
  exact jointKer_finrank φ Mg

end GlobalTheory.PtLocalEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
section
noncomputable section

open NumberField IsDedekindDomain Formalism.AUTREP Formalism.UG ReciprocityTheory.Aut

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K]

theorem antiJ_map (g : K →+* K) (n : ℕ) : (antiJ K n).map g = antiJ K n := by
  ext i j
  simp only [antiJ, Matrix.map_apply]
  split_ifs <;> simp

theorem cT_map (g σ σ' : K →+* K) (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : cT σ' (M.map g) = (cT σ M).map g := by
  ext i j
  simp [cT, hg]

def guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) (n : ℕ) :
    GU σ n →* GU σ' n :=
  ((bc (n := Fin n) (g : K →+* K)).comp (GU σ n).subtype).codRestrict (GU σ' n) (fun y => by
    have hy : cT σ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antiJ K n := y.2
    show cT σ' (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K)) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K) = antiJ K n
    rw [cT_map (g : K →+* K) σ σ' hg, ← antiJ_map (g : K →+* K) n]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hy])

theorem guMap_val (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (y : GU σ n) :
    (((guMap g hg n y : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map g := rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def gEquiv (D D' : InertDatum L n v w) : w.adicCompletion L ≃+* w.adicCompletion L :=
  D.e.symm.trans D'.e

theorem gEquiv_e (D D' : InertDatum L n v w) (y) : gEquiv D D' (D.e y) = D'.e y := by
  simp [gEquiv]

theorem gEquiv_comm (D D' : InertDatum L n v w) :
    ∀ x, gEquiv D D' (D.σw x) = D'.σw (gEquiv D D' x) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [← D.comm, gEquiv_e, gEquiv_e, D'.comm]

theorem gEquiv_intL (D D' : InertDatum L n v w) :
    ∀ x, x ∈ intL (w.adicCompletion L) ↔ gEquiv D D' x ∈ intL (w.adicCompletion L) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [gEquiv_e, ← D.integ, ← D'.integ]

end GlobalTheory.SatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyConductorBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem tupEtaInv_unrAt_splitOut : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∀ w, SplitOut X.nd i w → (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j _hj w hw
  obtain ⟨_hsplit, hl, hS, hQ⟩ := hw
  have hS' : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
      w ∈ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde))) := fun h =>
    hS ((X.nd.S_def i w).2 ⟨h, hl⟩)
  have hmu0 : (cf.mu0 j).UnrAt w := (cf.isMu0 j).unr w (fun k hk => by
    fin_cases k
    · exact hS' (Or.inl hk)
    · exact hS' (Or.inr (Or.inl hk)))
  have hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQeq : X.nd.Q i = C.Q (X.nd.w i) := (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
  have hpsi : (tp.psi (X.nd.w i)).UnrAt w :=
    ((tp.psi_is (X.nd.w i) (X.nd.w_tw i)).ram w).2 (by rw [← hQeq]; exact hQ)
  have hdel : (cf.delAt (D.what₂.places.resChar (X.nd.w i))).UnrAt w := by
    rw [X.nd.w_l i]
    unfold CharFrame.delAt
    split_ifs with h
    · exact cf.isDel'.unr w (fun hp => hS' (Or.inr (Or.inr (by rw [if_pos h]; exact hp))))
    · exact cf.isDel.unr w (fun hp => hS' (Or.inr (Or.inr (by rw [if_neg h]; exact hp))))
  have hxi : (tp.xi (X.nd.mu i)).UnrAt w := by
    rw [X.nd.mu_w i, tp.xi_tw]
    exact HChar.UnrAt.mul hdel hpsi
  exact HChar.UnrAt.mul (HChar.UnrAt.mul hmu0 hxi) (HChar.UnrAt.inv (cf.isEta.unr w))

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ResidueLocPlace

theorem norm_le_one_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) (y : O) :
    ‖f y‖ ≤ 1 := by
  have hy : IsIntegral ℤ_[p] y := Algebra.IsIntegral.isIntegral y
  let v := NormedField.valuation (K := Qbar p)
  have hmem : ∀ z : ℤ_[p], ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom) z ∈ v.integer := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    have : ‖algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])‖ ≤ 1 := by
      rw [PadicAlgCl.norm_extends p]; exact PadicInt.norm_le_one z
    exact_mod_cast this
  let φ : ℤ_[p] →+* v.integer := ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom).codRestrict v.integer hmem
  have hI : IsIntegral v.integer (f y) := by
    refine IsIntegral.map_of_comp_eq φ f ?_ hy
    ext z
    simp only [RingHom.comp_apply, hf]
    rfl
  have h := (Valuation.integer.integers v).mem_of_integral hI
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_lt_one_of_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) {y : O}
    (hy : y ∈ IsLocalRing.maximalIdeal O) : ‖f y‖ < 1 := by
  have hle : ∀ z : O, ‖f z‖ ≤ 1 := norm_le_one_of_finite f hf
  have hfp : ‖f (p : O)‖ = (p : ℝ)⁻¹ := by
    have h1 := hf (p : ℤ_[p])
    rw [map_natCast] at h1
    rw [h1, PadicAlgCl.norm_extends p]
    simp [Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hp0 : (p : O) ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hfp
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have := (Fact.out : p.Prime).pos; positivity
    linarith
  have hpu : ¬ IsUnit (p : O) := by
    rintro ⟨u, hu⟩
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one, hu, hfp] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h5 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, norm_zero]; exact zero_lt_one
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ
  obtain ⟨k, w, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have he : e ≠ 0 := by
    rintro rfl; apply hpu; rw [hpe, pow_zero, mul_one]; exact u.isUnit
  have hk : k ≠ 0 := by
    rintro rfl
    rw [hyk, pow_zero, mul_one] at hy
    exact (IsLocalRing.mem_maximalIdeal _).1 hy w.isUnit
  have hu1 : ‖f (u : O)‖ = 1 := by
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h6 := hle (u : O)
    have h5 : 0 ≤ ‖f (u : O)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  have key : y ^ e * (u : O) ^ k = (p : O) ^ k * (w : O) ^ e := by
    rw [hpe, hyk]; ring
  have hn := congrArg (fun z => ‖f z‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, hu1, one_pow, mul_one, hfp] at hn
  have hw := hle (w : O)
  have hA : ‖f y‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [hn]
    calc ((p : ℝ)⁻¹) ^ k * ‖f (w : O)‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := mul_one _
  have hB : ((p : ℝ)⁻¹) ^ k < 1 := pow_lt_one₀ (by positivity) hp1 hk
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 (lt_of_le_of_lt hA hB)

end GlobalTheory.ResidueLocPlace

namespace GlobalTheory.ResidueLocPlace

theorem exists_residue_lift {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (hp : p.Prime)
    (hq : q.Prime) (ι : Qbar p ≃+* ℂ) (B : ValuationSubring ℂ) (hB : ∀ z, z ∈ B ↔ ‖ι.symm z‖ ≤ 1)
    (κB : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar p)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[q] O]
    [Module.Finite ℤ_[q] O] (iq : FractionRing O →+* Qbar q)
    (iq_alg : ∀ z : ℤ_[q], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[q] O z)) =
      algebraMap ℚ_[q] (Qbar q) (z : ℚ_[q])) :
    ∃ κ : IsLocalRing.ResidueField O →+* Formalism.CyclotomicNorms.Fbar q, ∀ y : O,
      ∃ hy : (((qCast h ι).toRingHom.comp iq).comp (algebraMap O (FractionRing O))) y ∈ B,
        fbCast h hp hq (κB (IsLocalRing.residue B ⟨_, hy⟩)) = κ (IsLocalRing.residue O y) := by
  subst h
  let f : O →+* Qbar p := iq.comp (algebraMap O (FractionRing O))
  have hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := iq_alg
  have hmem : ∀ y, ι (f y) ∈ B := fun y =>
    (hB _).2 (by rw [RingEquiv.symm_apply_apply]; exact norm_le_one_of_finite f hf y)
  let g : O →+* B := (ι.toRingHom.comp f).codRestrict B.toSubring hmem
  let F : O →+* Formalism.CyclotomicNorms.Fbar p := κB.toRingHom.comp ((IsLocalRing.residue B).comp g)
  have hF : ∀ a ∈ IsLocalRing.maximalIdeal O, F a = 0 := by
    intro a ha
    have hlt := norm_lt_one_of_mem_maximalIdeal f hf ha
    have hg : g a ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h1 : ((u : B) : ℂ) * (((u⁻¹ : Bˣ) : B) : ℂ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      rw [hu] at h1
      have h2 : ι (f a) = ((g a : B) : ℂ) := rfl
      rw [← h2] at h1
      have h3 := congrArg (fun z => ‖ι.symm z‖) h1
      simp only [map_mul, RingEquiv.symm_apply_apply, norm_mul, map_one, norm_one] at h3
      have h4 : ‖ι.symm (((u⁻¹ : Bˣ) : B) : ℂ)‖ ≤ 1 := (hB _).1 (((u⁻¹ : Bˣ) : B)).2
      have h5 : 0 ≤ ‖f a‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    show κB (IsLocalRing.residue B (g a)) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hg, map_zero]
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) F hF, fun y => ⟨hmem y, rfl⟩⟩

end GlobalTheory.ResidueLocPlace

theorem GlobalTheory.ResidueLocPlace.exists_residueField_map : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  exact GlobalTheory.ResidueLocPlace.exists_residue_lift (X.nd.w_l i) _ _ (A.pl.ι (X.nd.w i)) (A.pl.plB (X.nd.w i))
    (A.pl.plB_eq (X.nd.w i)) (A.pl.plκ (X.nd.w i)) (Sp.iq i) (Sp.iq_alg i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalCondition
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeckePointUniq

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem eq_of_eigen : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (V : Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i))), V ≠ ⊥ → ∀ x x' : X.nd.X i, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) → (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x') • (mlX M X i).real y) → x = x' := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i V hV x x' hx hx'
  classical
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  have hry : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (by rw [h, map_zero]))
  have hιinj : Function.Injective (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp
      (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) :=
    ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).injective.comp (Sp.iq i).injective).comp
      (IsFractionRing.injective (X.nd.O i) (FractionRing (X.nd.O i)))
  have key : ∀ v k, SplitOut X.nd i v → 1 ≤ k → k ≤ D.R.nV →
      (X.nd.hT i v k : X.nd.X i → X.nd.O i) x = (X.nd.hT i v k : X.nd.X i → X.nd.O i) x' := by
    intro v k hv hk1 hk2
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
    have e1 := hx v k s ϖ hv hc hu hk1 hk2 y hyV
    have e2 := hx' v k s ϖ hv hc hu hk1 hk2 y hyV
    rw [e1] at e2
    exact hιinj (smul_left_injective ℂ hry e2)
  have hTle : X.nd.T i ≤ AlgHom.equalizer (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x)
      (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x') := by
    rw [← X.nd.T_gen i]
    refine Algebra.adjoin_le ?_
    rintro f ⟨v, k, h1, h2, h3, h4, hk1, hk2, rfl⟩
    exact key v k ⟨h1, h2, h3, h4⟩ hk1 hk2
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := X.nd.T_sep i x x' hne
  exact hfx (hTle hf)

end GlobalTheory.HeckePointUniq
end
end

