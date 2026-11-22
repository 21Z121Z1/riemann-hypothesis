import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormRowSubProdMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariantStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_character_translates_coinvariant : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  first | exact @GlobalTheory.RankFibre.coinv_or_fullRank_le | exact GlobalTheory.RankFibre.coinv_or_fullRank_le | (intros; apply GlobalTheory.RankFibre.coinv_or_fullRank_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTensorLatticeComponentIntegralStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_tensorLattice_component_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)),
    IsSplitBasis t X.L b → IsSplitBasis t W.L c → ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.LatInt.latAtV_comp_integral | exact GlobalTheory.LatInt.latAtV_comp_integral | (intros; apply GlobalTheory.LatInt.latAtV_comp_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorusCent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem swap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : IsWittFrame σ J Y X :=
  ⟨hW.yy, hW.xx, yx h hJ hW, fun z h1 h2 h3 => hW.aniso z h2 h1 h3⟩

theorem levi_swap (S : Finset (Fin r)) : levi σ J Y X S = levi σ J X Y S := by
  simp only [levi, inf_comm]

theorem comm_block (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {S : Finset (Fin r)}
    (hS : ∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) {g : GAd σ J} (hg : g ∈ levi σ J X Y S) (d : Fin r → AF F ⊗[F] E)
    (hd : ∀ k ∉ S, d k = 0) :
    (matHom _ σ J g).1 * (adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J)) =
      adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 := by
  have e1 : (matHom _ σ J g).1 * adMat F X * diagonal d = adMat F X * diagonal (fun k =>
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * d k) := by
    ext i k
    rw [mul_diagonal, mul_diagonal]
    by_cases hk : k ∈ S
    · have := congrFun (GlobalTheory.T.levi_element_preserves_witt_column_span h hJ hW hS hg k hk) i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_apply, this]
      ring
    · simp [hd k hk]
  have e2 : diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 =
      diagonal (fun k => (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * d k) *
        adMat F (cT (σ : E →+* E) Y * J) := by
    ext k i
    rw [Matrix.mul_assoc, diagonal_mul, diagonal_mul]
    by_cases hk : k ∈ S
    · have hg' : g⁻¹ ∈ levi σ J Y X S := by rw [levi_swap]; exact inv_mem hg
      rw [GlobalTheory.T.witt_frame_eigenvector_column_form h hJ hW _ (GlobalTheory.T.levi_element_preserves_witt_column_span h hJ (swap h hJ hW) hS hg' k hk) i]
      ring
    · simp [hd k hk]
  calc (matHom _ σ J g).1 * (adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J))
      = ((matHom _ σ J g).1 * adMat F X * diagonal d) * adMat F (cT (σ : E →+* E) Y * J) := by
        simp only [Matrix.mul_assoc]
    _ = adMat F X * (diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) := by
        rw [e1, e2]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem centre_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, (∀ k ∉ S, l k = 1) → IsIdTorusElt σ J X Y l a → a ∈ levi σ J X Y S ∧ ∀ m ∈ levi σ J X Y S, a * m = m * a := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW S hS l a hl ha
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((l (Fin.castLE k.2 i) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((l (Fin.castLE k.2 i))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ (l (Fin.castLE k.2 i)))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ (l (Fin.castLE k.2 i)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · apply matHom_injective
    apply Units.ext
    have hd1 : ∀ k ∉ S, ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = 0 := fun k hk => by simp [hl k hk]
    have hd2 : ∀ k ∉ S, (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = 0 := fun k hk => by simp [hl k hk]
    have c1 := comm_block h hJ hW hS hm _ hd1
    have c2 := comm_block h hJ (swap h hJ hW) hS (by rwa [levi_swap]) _ hd2
    simp only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq h hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, c1, c2]

end GlobalTheory.IdTorusCent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruen
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.StTwLevel

theorem finsum_const_mul {ι : Type} (c : ℂ) (g : ι → ℂ) : ∑ᶠ i, c * g i = c * ∑ᶠ i, g i := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases h : (Function.support g).Finite
  · exact (mul_finsum _ _).symm
  · have hs : Function.support (fun i => c * g i) = Function.support g := by
      ext i; simp [hc]
    rw [finsum_of_infinite_support h, mul_zero, finsum_of_infinite_support (by rwa [hs])]

theorem avg_const_mul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun h => c * u h) = c * avg u := by
  by_cases hc : c = 0
  · simp [hc, avg]
  have hR : rStab (fun h => c * u h) = rStab u := by
    ext k
    simp only [GlobalTheory.TwOrbConj.mem_rStab, mul_right_inj' hc]
  unfold avg
  rw [hR, finsum_const_mul]
  ring

theorem twOrb_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (c : ℂ)
    (f : G → ℂ) : twOrb θ K δ (fun x => c * f x) = c * twOrb θ K δ f := by
  unfold twOrb
  simp_rw [avg_const_mul]
  rw [← finsum_const_mul]
  refine finsum_congr fun q => ?_
  ring

theorem clSum_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G)
    (wt : G → ℂ) (c : ℂ) (f : G → ℂ) : clSum θ K S wt (fun x => c * f x) = c * clSum θ K S wt f := by
  unfold clSum
  rw [← finsum_const_mul]
  refine finsum_congr fun d => ?_
  split_ifs
  · rw [twOrb_const_mul]; ring
  · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stTw2_const_mul (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ)
    (φ : GLw a w × GLw b w → ℂ) : stTw2 a b w Q₁ Q₂ (fun y => c * φ y) = c * stTw2 a b w Q₁ Q₂ φ := by
  unfold stTw2
  exact clSum_const_mul _ _ _ _ _ _

def lev (n : ℕ) (w : Pl E) (k : ℕ) (y : GLw n w) : ℂ :=
  if y ∈ GlobalTheory.LFun.KGL w n ∧ nrmL n w y ∈ GlobalTheory.PrincCong.congSub w n k then 1 else 0

theorem nrm_eq {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (y : GLw n w) : nrmL n w y = y * thL n w y := by
  unfold nrmL thL
  rw [if_neg hw, if_neg hw]

theorem thL_KGL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w n) :
    thL n w g ∈ GlobalTheory.LFun.KGL w n := by
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  obtain ⟨h, rfl⟩ := hg
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (GlobalTheory.PrincCong.cj_mem_Ov w)
  exact ⟨thetaGL n c' h, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩

theorem conj_mem_congSub {w : Pl E} {n k : ℕ} {h g : GLw n w} (hh : h ∈ GlobalTheory.LFun.KGL w n)
    (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) : h * g * h⁻¹ ∈ GlobalTheory.PrincCong.congSub w n k := by
  obtain ⟨h', rfl⟩ := hh
  obtain ⟨g', hg', rfl⟩ := hg
  exact ⟨h' * g' * h'⁻¹, (MonoidHom.normal_ker _).conj_mem g' hg' h', by simp only [map_mul, map_inv]⟩

end GlobalTheory.BCT.StTwLevel

namespace GlobalTheory.BCT.StTwLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le {w : Pl E} {n k : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) :
    g ∈ GlobalTheory.LFun.KGL w n := ((GlobalTheory.PrincCong.mem_congSub_iff w n k g).1 hg).1

theorem lev_level {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.PrincCong.congSub w n k) :=
  ⟨GlobalTheory.PrincCong.isOpen_congSub w n k, fun _ hg => congSub_le hg, GlobalTheory.PrincCong.thL_mem_congSub w hw n k⟩

theorem lev_hecke {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsHecke (GlobalTheory.PrincCong.congSub w n k) (lev n w k) := by
  refine ⟨?_, fun x hx y => ⟨?_, ?_⟩⟩
  · have hc := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
    refine HasCompactSupport.intro' hc.2 (Subgroup.isClosed_of_isOpen _ hc.1) fun y hy => ?_
    unfold lev
    exact if_neg fun h => hy h.1
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w n
    · have hxy : x * y ∈ GlobalTheory.LFun.KGL w n := mul_mem hxK hy
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * thL n w x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hθx
      have e : nrmL n w (x * y) = x * nrmL n w y * ((thL n w y)⁻¹ * thL n w x * thL n w y) := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hm, Subgroup.mul_mem_cancel_left _ hx]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : x * y ∉ GlobalTheory.LFun.KGL w n := fun h => hy (by simpa using mul_mem (inv_mem hxK) h)
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w n
    · have hxy : y * x ∈ GlobalTheory.LFun.KGL w n := mul_mem hy hxK
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hx
      have e : nrmL n w (y * x) = nrmL n w y * ((thL n w y)⁻¹ * x * thL n w y) * thL n w x := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hθx, Subgroup.mul_mem_cancel_right _ hm]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : y * x ∉ GlobalTheory.LFun.KGL w n := fun h => hy (by simpa using mul_mem h (inv_mem hxK))
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩

theorem lev_eq {w : Pl E} (n k : ℕ) :
    (fun y : GLw n w => if y ∈ GlobalTheory.LFun.KGL w n ∧ nrmL n w y ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j,
      Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}
      then (1 : ℂ) else 0) = lev n w k := by
  funext y
  unfold lev
  exact if_congr (and_congr Iff.rfl (GlobalTheory.PrincCong.mem_congSub_iff w n k _).symm) rfl rfl

theorem stTw2_lev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  intro E _ _ _ w hw a b k Q₁ Q₂ c _ _ _ _ _
  rw [lev_eq a k, lev_eq b k]
  have e : (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then (1 : ℂ) else 0)) =
      fun y => c * GlobalTheory.BCT.tens (lev a w k) (lev b w k) y := by
    funext y
    congr 1
    have h1 := congrFun (lev_eq (w := w) a k) y.1
    have h2 := congrFun (lev_eq (w := w) b k) y.2
    rw [GlobalTheory.BCT.tens, ← h1, ← h2, ite_zero_mul_ite_zero, mul_one]
    exact if_congr and_assoc.symm rfl rfl
  rw [e, stTw2_const_mul, GlobalTheory.BCT.StTwTens.stTw2_tens E a b w Q₁ Q₂ _ _ _ _ (lev_level hw a k) (lev_level hw b k)
    (lev_hecke hw a k) (lev_hecke hw b k)]

end GlobalTheory.BCT.StTwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionInverseTransposeMaximalMinorProduct
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem substF_invT_minor_det {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} (X : Data P)
    (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ) (τ : D.what₂.Tau) (s : Fin P.a → Fin P.d) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det) =
      MvPolynomial.C ((G τ)⁻¹.det) * MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det := by
  set M := Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)
  set φ := GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
  set H : Matrix (Fin P.a) (Fin P.a) (MvPolynomial (FVar D X.B.rank X.A.rank) ℂ) :=
    Matrix.of fun i'' i' => MvPolynomial.C ((G τ)⁻¹ (Fin.cast X.rkA.symm i') (Fin.cast X.rkA.symm i''))
  have hH : H.det = MvPolynomial.C ((G τ)⁻¹.det) := by
    have e1 : H = (MvPolynomial.C : ℂ →+* MvPolynomial (FVar D X.B.rank X.A.rank) ℂ).mapMatrix
        (((G τ)⁻¹.transpose).submatrix (finCongr X.rkA.symm) (finCongr X.rkA.symm)) := by
      ext i j; simp [H]
    rw [e1, ← RingHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
  have hM : ((φ.comp (MvPolynomial.rename X.var)).mapMatrix M) = (MvPolynomial.rename X.var).mapMatrix M * H := by
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, M, H, Matrix.of_apply, AlgHom.comp_apply,
      MvPolynomial.rename_X, φ, GlobalTheory.CompactHowe.substF_X, Data.var]
    rw [Finset.sum_eq_single (Fin.cast X.rkB.symm (s i))]
    · simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
      exact Fintype.sum_equiv (finCongr X.rkA) _ _ (fun l => by simp [mul_comm])
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  have := AlgHom.map_det (φ.comp (MvPolynomial.rename X.var)) M
  rw [AlgHom.comp_apply] at this
  rw [this, hM, Matrix.det_mul, hH, ← AlgHom.map_det, mul_comm]

end GlobalTheory.NormDict

namespace GlobalTheory.NormDict

theorem substF_invT_minorPol : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P)
    (T : Tup D P.a P.d P.n) (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ),
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (minorPol D T)) =
      (∏ τ, ((G τ)⁻¹.det) ^ P.n τ) • MvPolynomial.rename X.var (minorPol D T) := by
  intro D cc δ t0 Q P X T G
  rw [minorPol, map_prod, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  simp only [substF_invT_minor_det, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

end GlobalTheory.NormDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionMaximalMinorProductEqSumCauchyBinet
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem substF_minorPol_eq_sum : ∀ (D : D7) {a d : ℕ} {m : D.what₂.Tau → ℕ} (K : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ)
    (T : Tup D a d m), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (minorPol D T) =
      ∑ T' : Tup D a d m, (∏ τ, ∏ r, (Matrix.of fun i i' : Fin a => K τ ((T' τ r).1 i') ((T τ r).1 i)).det) •
        minorPol D T' := by
  intro D a d m K T
  have hmin : ∀ τ (s : Fin a → Fin d), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))
      (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det =
      ∑ s' : {s : Fin a → Fin d // StrictMono s},
        MvPolynomial.C ((Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)).det) *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s'.1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det]
    have hM : (GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))).mapMatrix
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
        (Matrix.of fun (i : Fin a) (k : Fin d) => (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) *
        (Matrix.of fun (k : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, k, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) := by
      refine Matrix.ext fun i i' => ?_
      simp only [RingHom.mapMatrix_apply, AlgHom.coe_toRingHom, Matrix.map_apply, Matrix.of_apply,
        GlobalTheory.CompactHowe.substF_X, Matrix.mul_apply, Matrix.one_apply]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single i']
      · simp
      · intro l _ hl; simp [Matrix.one_apply_ne hl]
      · simp
    rw [hM, GlobalTheory.MinorFrame.det_mul_eq_sum_sm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    congr 1
    rw [show (Matrix.of fun (i : Fin a) (k : Fin d) =>
        (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).submatrix id s'.1 =
        (MvPolynomial.C : ℂ →+* MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ).mapMatrix
          (Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)) from by ext; simp]
    rw [← RingHom.map_det]
  unfold minorPol
  simp only [map_prod, hmin]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [← MvPolynomial.C_mul']
  simp only [Finset.prod_mul_distrib, map_prod]

end GlobalTheory.NormDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompMulLeftX
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polMap_tprod_eq_prod_rename_mulX (W Λ : Type) [Fintype W] [DecidableEq W] (q : W → MvPolynomial Λ ℂ) :
    GlobalTheory.CCRFock.polMap W Λ (PiTensorProduct.tprod ℂ q) =
      ∏ v, MvPolynomial.rename (Prod.mk v) (q v) := by
  simp [GlobalTheory.CCRFock.polMap]

theorem polMap_comp_atPl_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  intro W Λ _ _ w l
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  have h : GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (MvPolynomial.X l * p w)) := by
    unfold GlobalTheory.RealLift.atPl
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext v
    by_cases hv : v = w
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, h, polMap_tprod_eq_prod_rename_mulX,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Prod.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompPderiv
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.CCRFock

theorem pderiv_rename_prodMk_of_ne {W Λ : Type} {v w : W} (h : v ≠ w) (l : Λ) (r : MvPolynomial Λ ℂ) :
    MvPolynomial.pderiv (w, l) (MvPolynomial.rename (Prod.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Prod.fst e)

theorem pderiv_prod_rename_of_notMem {W Λ : Type} {w : W} (l : Λ) (q : W → MvPolynomial Λ ℂ) (s : Finset W)
    (hs : w ∉ s) :
    MvPolynomial.pderiv (w, l) (∏ v ∈ s, MvPolynomial.rename (Prod.mk v) (q v)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_prodMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMap_comp_atPl_pderiv (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ) :
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (w, l)).toLinearMap ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  apply PiTensorProduct.ext
  ext1 q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, polMap, atPl, PiTensorProduct.map_tprod,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i)
      ((Function.update (fun _ : W => (LinearMap.id : MvPolynomial Λ ℂ →ₗ[ℂ] MvPolynomial Λ ℂ)) w
        (MvPolynomial.pderiv l).toLinearMap i) (q i)) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), LinearMap.id_apply]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename (Prod.mk_right_injective w) l (q w)]
  simp [mul_comm]

end GlobalTheory.CCRFock
end
end

