import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0663
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowFock

theorem isThetaFunO_fock_right : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} {W : G'.Weil}, W.Over R → ∀ (ρ : RealMatch W), RealMatch.Over R ρ → ∀ (t : T) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f → ∀ Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank, IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (W.fock (.chi i j) f Q) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W _ ρ _ t i j hi hj e _ φ f hf Q
  have h₀ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (vacOf ρ (.right i j)) :=
    (ρ.vX_is i j hi hj).2.theta
  have hfθ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 h₀
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hfθ Q

end GlobalTheory.RowFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTypeAtDualParIffStarIsTypeAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TypeConj

open Matrix Formalism.IndefR.Mult GlobalTheory.ConjDS GlobalTheory.ConjMult

variable {D : D7}

theorem isTypeAt_star (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ)
    (h : IsTypeAt θ V τ P φ) : IsTypeAt θ V τ (dualPar P) fun g => star (φ g) := by
  obtain ⟨H, i1, i2, σ, lam, ε, Q, hE, hD, hQ, hG, hx⟩ := h
  letI := i1; letI := i2
  have hJ := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have e : ∀ g, rv (Q.submatrix Fin.revPerm (Equiv.refl _) * g * (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) =
      Q * g * Q⁻¹ := by
    intro g
    rw [inv_submatrix_equiv]
    have : Q.submatrix Fin.revPerm (Equiv.refl _) * g * Q⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (Q * g * Q⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  have hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : Cj H,
      cj H ((fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
        (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) w) = (fun g => σ (Q * g * Q⁻¹)) g (cj H w) := by
    intro g _ w
    show σ (rv _) (cj H w) = _
    rw [e]
  have hc' : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : H,
      (cj H).symm ((fun g => σ (Q * g * Q⁻¹)) g w) = (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
        (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) ((cj H).symm w) := by
    intro g hg w
    apply (cj H).injective
    rw [hc g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hfold : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w : Cj H,
      l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w) =
        cj H (l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons X l ih =>
      intro hl w
      rw [List.foldr_cons, ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_conj hJ (cj H) hc (hl X List.mem_cons_self),
        List.foldr_cons]
  have hn : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w : Cj H,
      ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w‖ =
        ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w)‖ := by
    intro l hl w
    rw [hfold l hl, LinearIsometryEquiv.norm_map]
  refine ⟨Cj H, inferInstance, inferInstance, fun g => cjOp (σ (rv g)), nr lam, fun a => ε a.rev,
    Q.submatrix Fin.revPerm (Equiv.refl _), isEnum_dual hE, isDS_transfer (fun _ => rfl) (cj H) (fun _ _ => rfl) hD,
    (Matrix.isUnit_submatrix_equiv _ _).2 hQ, ?_, fun x => ?_⟩
  · rw [← hG, ← rv_Jm (ε := fun a => ε a.rev) (ε' := ε) (fun a => by simp), rv,
      conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    rfl
  obtain ⟨v, hv, ℓ, hℓ, ⟨S, C, hS, hb, hsum, B, hB, hBb⟩, hs⟩ := hx x
  let ℓ' : ℕ → (Cj H →ₗ[ℂ] ℂ) := fun i =>
    { toFun := fun w => star (ℓ i (cj H w))
      map_add' := fun x y => by simp
      map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }
  refine ⟨fun i => (cj H).symm (v i), fun i => smoothVec_conj hJ (cj H).symm hc' (hv i), ℓ', fun i => ?_,
    ⟨S, C, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, fun g hg w hw => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨ℓ'', h1, h2⟩ := sobCont_conj hJ (cj H) hc (hℓ i)
    have : ℓ'' = ℓ' i := LinearMap.ext h2
    rw [← this]; exact h1
  · have h1 := hb i (cj H w) (smoothVec_conj hJ (cj H) hc hw)
    have h2 : (S.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w‖) = S.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w)‖ :=
      List.map_congr_left fun l hl => hn l (hS l hl) w
    rw [h2]
    exact (norm_star _).trans_le h1
  · have h2 : ∀ i, (S'.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) ((cj H).symm (v i))‖) =
        S'.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (v i)‖ := fun i =>
      List.map_congr_left fun l hl => by rw [hn l (hS' l hl), LinearIsometryEquiv.apply_symm_apply]
    simp only [h2]
    exact hsum S' hS'
  · have h2 := hc g hg w
    have h3 : ∀ u : Cj H, (S.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) u‖) = S.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H u)‖ :=
      fun u => List.map_congr_left fun l hl => hn l (hS l hl) u
    rw [h3, h3, h2]
    exact hBb g hg (cj H w) (smoothVec_conj hJ (cj H) hc hw)
  · have e2 : ∀ i, ℓ' i ((fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) ((cj H).symm (v i))) = star (ℓ i (σ (Q * g * Q⁻¹) (v i))) := by
      intro i
      show star (ℓ i (cj H _)) = _
      rw [hc g hg, LinearIsometryEquiv.apply_symm_apply]
    simp only [e2]
    exact (hs g hg).star

theorem isTypeAt_dualPar_iff : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ),
    IsTypeAt θ V τ (Formalism.IndefR.Mult.dualPar P) φ ↔ IsTypeAt θ V τ P fun g => star (φ g) := by
  intro D θ V τ P φ
  constructor
  · intro h
    have := isTypeAt_star θ V τ _ _ h
    rwa [dualPar_dualPar] at this
  · intro h
    have := isTypeAt_star θ V τ _ _ h
    simpa only [star_star] using this

end GlobalTheory.TypeConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedInvariantIntegralDoubleCosetCellSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.CellInt

theorem cellBot_iff {G : Type} [Group G] {R K : Subgroup G} {b x : G} :
    (∃ r ∈ R, ∃ a ∈ (⊥ : Subgroup G), ∃ k ∈ K, x = r * a * b * k) ↔ ∃ r ∈ R, ∃ k ∈ K, x = r * b * k := by
  constructor
  · rintro ⟨r, hr, a, ha, k, hk, rfl⟩
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact ⟨r, hr, k, hk, by simp⟩
  · rintro ⟨r, hr, k, hk, rfl⟩
    exact ⟨r, hr, 1, Subgroup.one_mem _, k, hk, by simp⟩

theorem cellWt_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (R K : Subgroup G) (ρ : Measure R) (μ : Measure G) (b : G) :
    cellWt ρ μ K b = (((μ (K : Set G)).toReal / (ρ (cellSet R K b b)).toReal : ℝ) : ℂ) := by
  simp only [cellWt, cellSet, measureReal_def, mul_assoc]

theorem niter_cellSum_at (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (R K : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (hl : l.Nodup)
    (hyp : ∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧
      (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) :
    ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ) (h : ∀ i, H i),
      (∀ β ∈ S, ∀ i, i ∉ l → b β i = h i) →
      (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q →
      (∀ g, (∀ i, i ∉ l → g i = h i) → q g ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) g) →
      NIter ρ μ q l h (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  induction l with
  | nil =>
    intro X S b q h hb hd _ hs
    simp only [NIter, List.map_nil, List.prod_nil, one_mul]
    have hbh : ∀ β ∈ S, b β = h := fun β hβ => funext fun i => hb β hβ i (by simp)
    have hsub : ∀ β ∈ S, ∀ β' ∈ S, β = β' := fun β hβ β' hβ' => hd β hβ β' hβ' (fun i hi => by simp at hi)
    by_cases hq : q h = 0
    · rw [hq]
      exact Finset.sum_eq_zero fun β hβ => by rw [hbh β hβ, hq]
    · obtain ⟨β, hβ, -⟩ := hs h (fun _ _ => rfl) hq
      rw [Finset.sum_eq_single β (fun β' hβ' hne => absurd (hsub β' hβ' β hβ) hne) (fun h' => absurd hβ h'), hbh β hβ]
  | cons i l' ih =>
    intro X S b q h hb hd hq hs
    classical
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨hcl, hkc, hko, hρ, hρi, hμ, hμr⟩ := hyp i (by simp)
    have hyp' : ∀ j ∈ l', _ := fun j hj => hyp j (List.mem_cons_of_mem _ hj)
    have hq' : BiInv R K l' q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
    have hne : ∀ j ∈ l', j ≠ i := fun j hj hji => hi (hji ▸ hj)
    set Wt' : X → ℂ := fun β => (l'.map fun j => cellWt (ρ j) (μ j) (K j) (b β j)).prod with hWt'
    have qinv : ∀ β g, g ∈ dcos (R i) (K i) (b β i) → q (Function.update (b β) i g) = q (b β) := by
      rintro β g ⟨r, hr, k, hk, rfl⟩
      have h1 := (hq i (by simp) (b β)).1 r hr
      have h2 := (hq i (by simp) (Function.update (b β) i (r * b β i))).2 k hk
      simp only [Function.update_self, Function.update_idem] at h2
      rw [h2, h1]
    refine ⟨fun g => ∑ β ∈ S, Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then 1 else 0), ?_, ?_⟩
    · haveI := hρ; haveI := hρi; haveI := hμ
      have hS := quotient_integral_finset_sum S (fun β g => Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then (1 : ℂ) else 0))
        (fun β => Wt' β * q (b β) * (((μ i (K i : Set (H i))).toReal / (ρ i (cellSet (R i) (K i) (b β i) (b β i))).toReal : ℝ) : ℂ))
        (fun β _ => by
          have := (isQuotientIntegral_indicator_doubleCoset (R i) (K i) hcl hkc hko (ρ i) (μ i) (b β i)).smul (Wt' β * q (b β))
          convert this using 1
          funext g
          simp [smul_eq_mul])
      convert hS using 1
      apply Finset.sum_congr rfl
      intro β _
      rw [List.map_cons, List.prod_cons, cellWt_eq (R i)]
      ring
    · intro g
      have key := ih hl' hyp' X (S.filter fun β => g ∈ dcos (R i) (K i) (b β i)) (fun β => Function.update (b β) i g) q
        (Function.update h i g) ?base ?dist hq' ?supp
      · convert key using 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro β _
        split_ifs with hg
        · have e : (l'.map fun j => cellWt (ρ j) (μ j) (K j) (Function.update (b β) i g j)).prod = Wt' β := by
            rw [hWt']
            congr 1
            apply List.map_congr_left
            intro j hj
            rw [Function.update_of_ne (hne j hj)]
          rw [e, qinv β g hg, mul_one]
        · simp
      case base =>
        intro β hβ j hj
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hb β (Finset.mem_filter.1 hβ).1 j (by simp [hji, hj])
      case dist =>
        intro β hβ β' hβ' hc
        obtain ⟨hβS, hgβ⟩ := Finset.mem_filter.1 hβ
        obtain ⟨hβS', hgβ'⟩ := Finset.mem_filter.1 hβ'
        refine hd β hβS β' hβS' ?_
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [cellBot_iff]
          have e1 := dcos_eq_of_mem hgβ
          have e2 := dcos_eq_of_mem hgβ'
          have hm : b β' j ∈ dcos (R j) (K j) (b β' j) := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
          rw [← e2, e1] at hm
          exact hm
        · obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j hj'
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj')] using e
      case supp =>
        intro g' hg' hq0
        have hgi : g' i = g := by simpa using hg' i hi
        obtain ⟨β, hβ, hc⟩ := hs g' (fun j hj => by
          have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
          have := hg' j (fun hj' => hj (List.mem_cons_of_mem _ hj'))
          rwa [Function.update_of_ne hji] at this) hq0
        refine ⟨β, Finset.mem_filter.2 ⟨hβ, ?_⟩, ?_⟩
        · have := hc i (by simp)
          rw [cellBot_iff, hgi] at this
          exact this
        · intro j hj
          obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j (List.mem_cons_of_mem _ hj)
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj)] using e

theorem niter_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  intro ι _ H _ _ _ _ _ _ _ _ R K l hl ρ μ hyp X S b q hb hd hq hs
  exact niter_cellSum_at ι H R K ρ μ l hl hyp X S b q 1 (fun β hβ i hi => by simpa using hb β hβ i hi) hd hq
    (fun g hg => hs g (fun i hi => by simpa using hg i hi))

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastBiExpand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LastSeeSawGen.lastBi_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (ρ : ℕ) (B : GlobalTheory.Unf.BesLev D ρ) (W X T L'' : HSp D) (o'' : OrthDec X T L'') (τ : Matrix (Fin B.L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (B.L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (a : k) (z₀ : Fin L''.rank → k), a ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * a)) • (fun i => p.pr (B.ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (Z : Type) [Fintype Z] [DecidableEq Z] (FA : GlobalTheory.LocMod.Frame k B.A.rank n') (F₀ : GlobalTheory.LocMod.Frame k B.V₀.rank (n' ⊕ Unit)) (FS : GlobalTheory.LocMod.Frame k W.rank n) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (FX : GlobalTheory.LocMod.Frame k X.rank (Z ⊕ Unit)), p.IsCoreFrame B a FA F₀ → FX.β = fromCols (o''.iA.map p.pr * FT.β) (Matrix.of fun r _ => (o''.iB.map p.pr *ᵥ z₀) r) → ∀ T₁ T₂, p.IsModel ψ F₀ FS T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n n' k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix (Z ⊕ Unit) n k)) (c₁ : I → WO B.A W →₀ ℂ) (c₂ : I → WO W X →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ FA FS (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ FS FX (c₂ i) (Ξ₂ i).1) → (∀ (y : Matrix n n' k) (y' : Matrix (Z ⊕ Unit) n k), Φ₂.1 y'.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun u => Φ₁.1 (fromCols y (Matrix.of fun r _ => u r))) (y' (Sum.inr ())) = ∑ i ∈ S, x i * ((Ξ₁ i).1 y * (Ξ₂ i).1 y')) → GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = ∑ i ∈ S, x i • biComb ψ B.A W X (c₁ i) (c₂ i) (GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂)) := by
  classical
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond ρ B W X T L'' o'' τ hL hτ a z₀ ha hz n _ _ n' _ _ Z _ _
    FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hrel
  have := hν.1
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.LastKerLoc.lastLoc D k p ν hν.1 ψ hstd ψk hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    n n' Z FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hv1 : valuation k (-1 : k) = 1 := by simp
  haveI : T2Space (Matrix n n' k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  haveI : T2Space (Matrix (Z ⊕ Unit) n k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  let P : I → SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) := fun i =>
    ⟨fun q => (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2,
      GlobalTheory.FinPl.Comm.prod_mem_SB (Ξ₁ i).2 (Ξ₂ i).2 continuous_fst continuous_snd continuous_id fun _ => rfl⟩
  let O₁' : SB (Matrix n n' k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Z ⊕ Unit) n k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int hcond hν hv1]
    simp only [O₁', O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  have hsum : Ξ = ∑ i ∈ S, x i • P i := by
    apply Subtype.ext
    funext q
    rw [hΞ q, hrel q.1 q.2, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have key : ∀ i ∈ S, Λ (P i) = biComb ψ B.A W X (c₁ i) (c₂ i) (Λ Ξ') := fun i hi =>
    (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ n n' (Z ⊕ Unit)).1 B.A W X FA FS FX Λ (c₁ i) (c₂ i) (Ξ₁ i) O₁'
      (Ξ₂ i) O₂' (P i) Ξ' hΛ (hc i hi).1 (hc i hi).2 rfl rfl (fun _ => rfl) hone
  have e1 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = Λ Ξ := funext fun u => hΞK u
  have e2 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂) = Λ Ξ' := funext fun u => hΞ'K u
  rw [e1, e2, hsum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, key i hi]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevJGridSuccIndep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem levJ_grid_succ_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (i j : ℕ) :
    levJ G t (.grid (i + 1) (j + 1)) = levJ G t' (.grid (i + 1) (j + 1)) := rfl

theorem levJ_top_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (j : ℕ) :
    levJ G t (.top j) = levJ G t' (.top j) := by
  cases j <;> rfl

theorem vol_row_top_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (M M' : Vol G), M.Is t → M'.Is t' → (∀ j, 1 ≤ j → j ≤ D.R.m → M.ν (.grid D.R.m j) = M'.ν (.grid D.R.m j)) ∧ ∀ j, j ≤ D.R.m → M.ν (.top j) = M'.ν (.top j) := by
  intro D T L sc G t t' M M' hM hM'
  refine ⟨fun j hj1 hjm => ?_, fun j hj => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, D.R.m = i + 1 := ⟨D.R.m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hX : levJ G t (.grid D.R.m (j' + 1)) = levJ G t' (.grid D.R.m (j' + 1)) := by
      rw [hi]; exact levJ_grid_succ_indep G t t' i j'
    have h1 := hM.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    have h2 := hM'.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    rw [← hX] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2
  · have h1 := hM.vtx (.top j) hj
    have h2 := hM'.vtx (.top j) hj
    rw [← levJ_top_indep G t t' j] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol ψ τ,
          (∃ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁) ∧
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.RealLieFock.lie_deriv_pol | exact GlobalTheory.RealLieFock.lie_deriv_pol | (intros; apply GlobalTheory.RealLieFock.lie_deriv_pol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsArchimedeanIdentityStatement
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
theorem _root_.GlobalTheory.T.matched_maps_archimedean_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ R.Pi,
      (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
        R.p f ∈ N → R.p f₁ ∈ N) →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.W Bs.emb, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N := by
  first | exact @GlobalTheory.KStableLie.lieStable_kStable | exact GlobalTheory.KStableLie.lieStable_kStable | (intros; apply GlobalTheory.KStableLie.lieStable_kStable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentityStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_gaussian_identity : GlobalTheory.Published.HoweDualityFinite →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, IsEmpty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  first | exact @GlobalTheory.HoweNonsplitKerSmall.howe_nonsplit_ker_small | exact GlobalTheory.HoweNonsplitKerSmall.howe_nonsplit_ker_small | (intros; apply GlobalTheory.HoweNonsplitKerSmall.howe_nonsplit_ker_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowCover

theorem mem_GfC_of_hasLoc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → x ∈ GfC _ := by
  intro D T L sc G t B j hj x g hx
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hg, -⟩ := hx
  have h0 : infPart D ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) = 0 := by
    rw [map_sum (cA D), ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := (hes PP hPP).1
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end GlobalTheory.RowCover
end
end

