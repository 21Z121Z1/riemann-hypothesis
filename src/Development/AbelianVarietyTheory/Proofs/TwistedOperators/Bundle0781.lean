import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdCharSymplecticRealAdelicPointsModelForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

variable {D : D7}

theorem gram_inv_eq (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) :
    (HSpace.gram V)⁻¹ = b * bᴴ := by
  have h1 : bᴴ * (HSpace.gram V * b) = 1 := by
    refine Matrix.ext fun a a' => ?_
    have := hb.1 a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Finset.mul_sum] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : (HSpace.gram V * b) * bᴴ = 1 := mul_eq_one_comm.1 h1
  rw [Matrix.mul_assoc] at h2
  exact Matrix.inv_eq_right_inv h2

theorem infPart_realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (realPt S T X i j) = infPart D (incA D (X i j)) := rfl

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [← h4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

end GlobalTheory.ArchPhase

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000

def hRat (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  Matrix.trace ((HSpace.gram S)⁻¹ * Yᴴ * HSpace.gram T * X)

theorem infPart_cA_realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) : infPart D (cA D (realPt S T X i j)) = infPart D (incA D (star (X i j))) := by
  rw [GlobalTheory.PhaseReal.infPart_cA, infPart_realPt, ← GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.DualPairCheck.cA_incA]

theorem infPart_hO_realPt (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    infPart D (hO S T (realPt S T X) (realPt S T Y)) = infPart D (incA D (hRat S T X Y)) := by
  rw [GlobalTheory.PhaseReal.hO_eq_trace, hRat]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, infPart_realPt, infPart_cA_realPt]

theorem finPart_hO_realPt (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finPart D (hO S T (realPt S T X) (realPt S T Y)) = 0 := by
  have h : ∀ i j, finPart D (realPt S T X i j) = 0 := fun i j =>
    congrFun (congrFun (GlobalTheory.FrameConst.realPt_fin S T X) i) j
  simp only [hO, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem hermitian_column_sum_neg_mul_rearrange {n : ℕ} (ξ u : D.host.E) (v : Fin n → D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) (c : Fin n) :
    - -ξ * ∑ x, u * -G x c * ReciprocityTheory.ChartRestriction.G.FD.cc (v x) = -(ξ * ((∑ j, star (v j) * G j c) * u)) := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hst : star (v x) = ReciprocityTheory.ChartRestriction.G.FD.cc (v x) := rfl
  rw [hst]
  ring

theorem sum_herm_eq (V W : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (r : ℕ)
    (hr : W.rank = r) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (hX : ModelW W hr X)
    (Xm Ym : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    ∑ a, (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (fun m => ∑ n, Xm (Fin.cast hr.symm m) n * b n a)
        (fun m => ∑ n, Ym (Fin.cast hr.symm m) n * b n a)) = -(D.host.xi0 * hRat V W Xm Ym) := by
  subst hr
  obtain ⟨hG, hξ⟩ := hX
  have e1 : hRat V W Xm Ym = Matrix.trace ((Ym * b)ᴴ * HSpace.gram W * (Xm * b)) := by
    rw [hRat, gram_inv_eq V b hb, Matrix.conjTranspose_mul, Matrix.mul_assoc b, Matrix.mul_assoc b,
      Matrix.mul_assoc b, Matrix.trace_mul_comm b]
    simp only [Matrix.mul_assoc]
  rw [e1, hξ, hG, Matrix.trace, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.neg_apply,
    Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply, Fin.cast_eq_self]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  exact hermitian_column_sum_neg_mul_rearrange (n := W.rank) _ _ (fun j : Fin W.rank => ∑ k : Fin V.rank, Ym j k * b k a) _ c

end GlobalTheory.ArchPhase

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

set_option synthInstance.maxHeartbeats 400000 in

theorem psi_symplOH_realPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D)
    (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis V b → ∀ (r : ℕ) (hr : W.rank = r)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r), ModelW W hr X → ∀ (Xm Ym : Matrix (Fin W.rank) (Fin V.rank) D.host.E),
    ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Xm) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Ym)) =
      Complex.exp (Real.pi * Complex.I * ∑ a, ((Algebra.trace ℚ D.host.E (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
        (fun m => ∑ n, Xm (Fin.cast hr.symm m) n * b n a) (fun m => ∑ n, Ym (Fin.cast hr.symm m) n * b n a)) : ℚ) : ℂ)) := by
  intro D ψ hψ V W b hb r hr X hX Xm Ym
  obtain ⟨θ, hθ⟩ := hψ.2.1
  set t := incA D D.host.xi0 * hO V W (realPt V W Xm) (realPt V W Ym) with ht
  have hfin : finPart D t = 0 := by rw [ht, map_mul, finPart_hO_realPt, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have hθt : ∀ ρ, θ ρ (infPart D t) = tauE D ρ (D.host.xi0 * hRat V W Xm Ym) := fun ρ => by
    rw [ht, map_mul (infPart D), infPart_hO_realPt, ← map_mul (infPart D), ← map_mul (incA D)]
    exact (hθ ρ).1 _
  have hL : symplOH V W (realPt V W Xm) (realPt V W Ym) =
      pairA D.host.F (algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) 0 := by
    unfold symplOH symplO
    rw [← ht, ← hTdef, hT]
    exact Prod.ext rfl (mul_zero _)
  have hs : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      (1 / 2 : ℂ) * ((2 * (tauE D ρ (D.host.xi0 * hRat V W Xm Ym)).re : ℝ) : ℂ) := fun ρ => by
    rw [show (algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E) =
        ((algebraMap D.host.F (Ainf D.host.F) (1 / 2)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
          ((fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E)) by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
      map_mul, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, hθt, GlobalTheory.StdRat.tmul_one_eq, (hθ ρ).1]
    congr 1
    simp only [one_div, map_inv₀]
    rw [map_ofNat (algebraMap D.host.F D.host.E) 2, map_ofNat]
  rw [hL]
  change psiInf D.host.F ψ _ = _
  rw [hψ.2.2 θ hθ]
  simp only [hs]
  rw [← Finset.mul_sum, sum_two_re_tauE, ← Rat.cast_sum, ← map_sum, sum_herm_eq V W b hb r hr X hX Xm Ym, map_neg]
  congr 1
  push_cast
  ring

end GlobalTheory.ArchPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaDictionaryLatticeOfFrameCoordinates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.DictLatPin

variable {D : D7}

theorem latFrame_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r)
    {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r}
    (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      ∀ τ : (X (dict h).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1)
    (g : GA D W) : ∃ γ ∈ GQ W,
      ((X (castDict hV dict g).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin W.rank → D.host.E => v ∘ Fin.cast hr'.symm) '' (latG W (γ * g) : Set _) ∧
      ∀ τ : (X (castDict hV dict g).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (castDict hV dict g).2 τ =
        Matrix.reindex (finCongr hr') (finCongr hr') (archM W (th (castDict hV dict g).1 τ) (γ * g)) * x₀ τ.1 := by
  subst hV
  exact h g

end GlobalTheory.DictLatPin

open GlobalTheory.DictLatPin in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.DictLatPin.lat_of_frAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i),
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ v : Fin D.R.r → D.host.E,
      v ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).Λ ↔
        (fun m => v (Fin.cast (rank_Wc i) m)) ∈ latG (Wc D i) (γ * g) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ _ hMods _ hT i σ hσ hV γ hγ g hFr v
  subst hσ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hL := hT.laws
  have hg := T.toCore.good_σ₀
  have hP := hL.pins
  obtain ⟨hr, g', e, F', ik, φ, th, -, -, hth, hD⟩ := hL.adPin _ hj _ hg
  have hcl := latFrame_cast hV hr (rank_Wc i) (T.dict ((i : ℕ) + 1) T.σ₀) th (T.x₀ ((i : ℕ) + 1) T.σ₀)
    (fun h => by
      obtain ⟨γ₁, hq, hl, -, hf⟩ := hD.2 h
      exact ⟨γ₁, hq, hl, hf⟩) g
  obtain ⟨γ', hγ', hΛ, hf'⟩ := hcl

  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  set k := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i T.σ₀ hV g).1 with hk
  have hU := hL.unf _ hj _ hg
  have hΨ := (hU.2.1 k).2
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hτ₀ : tauE D ρ₀ ∈ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := (hΨ _).2 (hP.1.2.2.2 ρ₀)
  let τ₀ : ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := ⟨tauE D ρ₀, hτ₀⟩
  have h1 := hFr ρ₀ τ₀ rfl
  have h2 := hf' τ₀
  have hth' : th k τ₀ = R.θ ρ₀ := GlobalTheory.LettersCheck.isInfEmb_unique (tauE D ρ₀) _ _ (hth k τ₀) (hMods.inf ρ₀)
  rw [← hx.mul] at h1
  rw [hth'] at h2
  have h3 : Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ' * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) := h2.symm.trans h1
  have hx₀ : IsOrthogonalFrame ((T.U ((i : ℕ) + 1) T.σ₀).X k) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hL.familyUniformisationBasePointOrthogonal _ hj _ hg k
  obtain ⟨-, hu2, -⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).p0 ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm_herm
  have hdet : IsUnit (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀)).det :=
    (((hu2 (fun τ => T.x₀ ((i : ℕ) + 1) T.σ₀ τ.1) fun τ => hx₀ τ.1 τ.2).1 τ₀).1).isUnit
  have h4 : archM (Wc D i) (R.θ ρ₀) (γ' * g) = archM (Wc D i) (R.θ ρ₀) (γ * g) := by
    have := congrArg (· * (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀))⁻¹) h3
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hdet] at this
    exact (Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i))).injective this
  have h5 : ∀ δ : GA D (Wc D i), archM (Wc D i) (R.θ ρ₀) δ =
      archM (Wc D i) (R.θ ρ₀) (δ * g) * archM (Wc D i) (R.θ ρ₀) g⁻¹ := fun δ => by
    rw [← GlobalTheory.PointAtPlace.archM_mul, mul_inv_cancel_right]
  have hγγ : γ' = γ := GlobalTheory.AdTh.MarkUniq.rat_eq_of_archM (Wc D i) hγ' hγ (tauE D ρ₀) (R.θ ρ₀) (hMods.inf ρ₀)
    (by rw [h5 γ', h5 γ, h4])
  subst hγγ
  rw [← SetLike.mem_coe, hΛ]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ latG (Wc D i) (γ' * g) := hw
    convert hw' using 1
    funext m
    simp
  · intro hv
    exact ⟨_, hv, funext fun m => by simp⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOrientedModelEqOfRealAdelicPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped TensorProduct

namespace GlobalTheory.ThetaUniqReal

variable {D : D7}

theorem denseRange_hostField_infinite_finite_adelePair : DenseRange (fun z : D.host.F × D.host.F =>
    (pairA D.host.F (algebraMap D.host.F (Ainf D.host.F) z.1) (algebraMap D.host.F (Af D.host.F) z.2) : AF D.host.F)) :=
  (InfiniteAdeleRing.denseRange_algebraMap (K := D.host.F)).prodMap
    (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing D.host.F)

theorem pairA_alg (u v : D.host.F) :
    (pairA D.host.F (algebraMap D.host.F (Ainf D.host.F) u) (algebraMap D.host.F (Af D.host.F) v) : AF D.host.F) =
      algebraMap D.host.F (AF D.host.F) v + pairA D.host.F 1 0 * algebraMap D.host.F (AF D.host.F) (u - v) := by
  have h1 : ∀ x, (algebraMap D.host.F (AF D.host.F) x).1 = algebraMap D.host.F (Ainf D.host.F) x := fun _ => rfl
  have h2 : ∀ x, (algebraMap D.host.F (AF D.host.F) x).2 = algebraMap D.host.F (Af D.host.F) x := fun _ => rfl
  refine Prod.ext ?_ ?_
  · change algebraMap D.host.F (Ainf D.host.F) u = (algebraMap D.host.F (AF D.host.F) v).1 +
      1 * (algebraMap D.host.F (AF D.host.F) (u - v)).1
    rw [h1, h1, one_mul, map_sub]; ring
  · change algebraMap D.host.F (Af D.host.F) v = (algebraMap D.host.F (AF D.host.F) v).2 +
      0 * (algebraMap D.host.F (AF D.host.F) (u - v)).2
    rw [h2, zero_mul, add_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem alg_smul_tmul (p : AF D.host.F) (w : D.host.F) (e : D.host.E) :
    (p * algebraMap D.host.F (AF D.host.F) w) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) = p ⊗ₜ[D.host.F] (w • e) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem alg_smul_tmul_one (w : D.host.F) (e : D.host.E) :
    algebraMap D.host.F (AF D.host.F) w • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) = (1 : AF D.host.F) ⊗ₜ[D.host.F] (w • e) := by
  have h := alg_smul_tmul (D := D) 1 w e
  rwa [one_mul] at h

theorem denseRange_rat_add_real : DenseRange (fun p : D.host.E × D.host.E =>
    (incA D p.1 + pairA D.host.F 1 0 ⊗ₜ[D.host.F] p.2 : AE D)) := by
  classical
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  set b := Module.finBasis D.host.F D.host.E
  set Bt := Algebra.TensorProduct.basis (AF D.host.F) b
  let Φ : (Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) → AE D := fun α => ∑ k, α k • Bt k
  have hΦc : Continuous Φ := continuous_finset_sum _ fun k _ => (continuous_apply k).smul continuous_const
  have hΦs : Function.Surjective Φ := fun x => ⟨Bt.repr x, Bt.sum_repr x⟩
  have hd := hΦs.denseRange.comp (DenseRange.piMap fun _ => denseRange_hostField_infinite_finite_adelePair (D := D)) hΦc
  refine hd.mono ?_
  rintro _ ⟨z, rfl⟩
  refine ⟨((∑ k, (z k).2 • b k : D.host.E), (∑ k, ((z k).1 - (z k).2) • b k : D.host.E)), ?_⟩
  simp only [Function.comp_apply, Pi.map_apply, Φ, Bt, Algebra.TensorProduct.basis_apply, pairA_alg, add_smul,
    Finset.sum_add_distrib, alg_smul_tmul, alg_smul_tmul_one]
  congr 1
  · simp only [incA, inclR, map_sum]
    exact Finset.sum_congr rfl fun k _ => rfl
  · rw [TensorProduct.tmul_sum]

end GlobalTheory.ThetaUniqReal

namespace GlobalTheory.ThetaUniqReal

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem denseRange_ratW_add_realPt {D : D7} (S T : HSp D) :
    DenseRange (fun p : Fin T.rank → Fin S.rank → D.host.E × D.host.E =>
      (ratW T S (Matrix.of fun i j => (p i j).1) + realPt S T (Matrix.of fun i j => (p i j).2) : WO S T)) := by
  have h := DenseRange.piMap fun (_ : Fin T.rank) =>
    DenseRange.piMap fun (_ : Fin S.rank) => denseRange_rat_add_real (D := D)
  have e : (fun p : Fin T.rank → Fin S.rank → D.host.E × D.host.E =>
      (ratW T S (Matrix.of fun i j => (p i j).1) + realPt S T (Matrix.of fun i j => (p i j).2) : WO S T)) =
      fun p => Matrix.of fun i j => (incA D (p i j).1 + pairA D.host.F 1 0 ⊗ₜ[D.host.F] (p i j).2 : AE D) := by
    funext p; ext i j; simp [ratW, realPt]
  rw [e]
  exact h

theorem eq_of_eq_realPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : WO S T → ℂ),
    IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ →
    (∀ X : Matrix (Fin T.rank) (Fin S.rank) D.host.E, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X) = f₂ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X)) →
    f₁ = f₂ := by
  intro D ψ _ S T f₁ f₂ h₁ h₂ h
  refine (denseRange_ratW_add_realPt S T).equalizer h₁.cont h₂.cont (funext fun p => ?_)
  simp only [Function.comp_apply]
  rw [h₁.quasi, h₂.quasi, h]

end GlobalTheory.ThetaUniqReal
end
end

