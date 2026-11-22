import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0372
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0350
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0364
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeAutomorphismsEqAdaptedModUnipotent
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardExactGramIntegralFrameClassesLe
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC GlobalTheory.LoopC.FrEqv
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrEx

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  have := S.herm.eq x y
  rw [h, map_zero] at this
  exact this.symm

theorem mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

def moveFl (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) : LFlag S r T :=
  ⟨⟨fun a => n (F.fl.e a), n F.fl.z,
    F.fl.e_indep.map' (n : S.V →ₗ[E] S.V) n.ker,
    fun a b => (hn _ _).trans (F.fl.e_iso a b), fun a => (hn _ _).trans (F.fl.z_orth a),
    (hn _ _).trans F.fl.z_norm⟩, n F.fl.z⟩

theorem frame_moveFl (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (b : Fin (r + 1)) :
    frame (moveFl n hn F) b = n (frame F b) := by
  refine Fin.lastCases ?_ (fun a => ?_) b <;> simp [frame, FlagG.fvec, moveFl]

theorem eq_zero_of_orth_frame (F : LFlag S r T) (F' : LFlag S r T') (b₀ : Fin (r + 1))
    (hd : (((ZhatL F F').submatrix Fin.castSucc id).submatrix id b₀.succAbove).det ≠ 0)
    {x : S.V} (hx : x ∈ Xsp F) (h : ∀ b, S.hT x (frame F' b) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  have h0 : (fun a => star (c a)) = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero hd ?_
    funext b
    have := h (b₀.succAbove b)
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at this
    simpa [Matrix.vecMul, dotProduct, Zhat, brS, FlagG.fvec] using this
  have : ∀ a, c a = 0 := fun a => by simpa using congrFun h0 a
  simp [this]

theorem orth_frame_of_mem_Thp {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' : LFlag S r T'}
    (hl : IsLift Λ F') (he : ∀ a, F'.fl.e a ∈ Λ) {θ : S.V} (hθ : θ ∈ Thp Λ F F') (b : Fin (r + 1)) :
    S.hT θ (frame F' b) = 0 := by
  refine hT_swap (mem_orth.1 hθ.2 _ (Submodule.subset_span ?_))
  refine Fin.lastCases ?_ (fun a => ?_) b
  · have : frame F' (Fin.last r) = F'.zt := by simp [frame, FlagG.fvec, hl.2]
    rw [this]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · have : frame F' a.castSucc = F'.fl.e a := by simp [frame, FlagG.fvec]
    rw [this]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨he a, Submodule.subset_span ⟨a, rfl⟩⟩)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem eq_zero_of_span_E {x : (hS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE))
    (h : ∀ a, (hS D).hT x (D.sp.hypF a) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  have : ∀ a, c a = 0 := fun a => by
    have := h a
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      D.sp.hyp_ef] at this
    simpa using this
  simp [this]

theorem eq_zero_of_span_F {x : (hS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypF))
    (h : ∀ a, (hS D).hT (D.sp.hypE a) x = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  have : ∀ a, c a = 0 := fun a => by
    have := h a
    simp only [map_sum, map_smul, smul_eq_mul, D.sp.hyp_ef] at this
    simpa using this
  simp [this]

theorem YS_le {y : (hS D).V} (hy : y ∈ YS D) : y ∈ Submodule.span D.host.E (Set.range D.sp.hypF) := by
  have : YS D ≤ toO (hS D) (Submodule.span D.host.E (Set.range D.sp.hypF)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, _, rfl⟩
    exact Submodule.smul_mem (Submodule.span D.host.E (Set.range D.sp.hypF)) x (Submodule.subset_span ⟨a, rfl⟩)
  exact this hy

theorem XS_le {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {y : (hS D).V} (hy : y ∈ XS D F0) : y ∈ F0.X := by
  have : XS D F0 ≤ toO (hS D) F0.X := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, _, rfl⟩
    exact Submodule.smul_mem F0.X x (Submodule.subset_span ⟨a, rfl⟩)
  exact this hy

theorem iXY_mem_of_split {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE) {Λ : LatV D}
    (hs : IsSplit D F0 Λ) (p : (D.sp.X 0).V) {θ : (hS D).V} (hθ : θ ∈ Λ) (hx : θ - D.sp.iXY 0 p ∈ F0.X) :
    D.sp.iXY 0 p ∈ Λ := by
  have hθ' := hθ
  rw [hs] at hθ'
  obtain ⟨_, h1, y, hy, rfl⟩ := Submodule.mem_sup.1 hθ'
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 h1
  have haX := XS_le D F0 ha
  have hX : ∀ x ∈ F0.X, ∀ i, (hS D).hT (D.sp.hypE i) x = 0 := fun x hx i =>
    mem_orth.1 (X_le_orth (F := lf D F0) hx) _ (Submodule.subset_span ⟨i, by rw [← he]⟩)
  have hwE : ∀ i, (hS D).hT (D.sp.hypE i) w = 0 := fun i =>
    mem_orth.1 hw.2 _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
  have hwF : ∀ i, (hS D).hT (D.sp.hypF i) w = 0 := fun i =>
    mem_orth.1 hw.2 _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
  have hy0 : y = 0 := by
    refine eq_zero_of_span_F D (YS_le D hy) fun i => ?_
    have h1 := hX _ hx i
    have h2 : (hS D).hT (D.sp.hypE i) (D.sp.iXY 0 p) = 0 := hT_swap (D.sp.hyp_orthX i p).1
    rw [map_sub, map_add, map_add, h2, hX a haX i, hwE i] at h1
    simpa using h1
  subst hy0
  have h3 : w - D.sp.iXY 0 p ∈ F0.X := by
    have := F0.X.sub_mem hx haX
    convert this using 1
    abel
  have h4 : w - D.sp.iXY 0 p = 0 := by
    refine eq_zero_of_span_E D (by rw [← he]; exact h3) fun i => ?_
    rw [map_sub, LinearMap.sub_apply, hT_swap (hwF i)]
    have := (D.sp.hyp_orthX i p).2
    simpa using this
  rw [← sub_eq_zero.1 h4]
  exact hw.1

theorem exists_lift {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE) {Λ : LatV D}
    (hs : IsSplit D F0 Λ) (P : LatW D) (Z : GramM D) (b₀ : Fin (D.R.rS + 1)) (hb : rowMinor D Z b₀ ≠ 0)
    {F' : Fg D T'} (hF : F' ∈ ExSet D Λ (lf D F0) T' Z P) :
    ∃ φ : P →ₗ[𝓞 D.host.E] (hS D).V, (∀ p, φ p ∈ XLam Λ (lf D F0)) ∧
      ∀ (p : P) b, (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) (frame F' b) = 0 := by
  obtain ⟨hl, hE, hZ, hP⟩ := hF
  have ex : ∀ p : P, ∃ x, x ∈ XLam Λ (lf D F0) ∧
      ∀ b, (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + x) (frame F' b) = 0 := by
    intro p
    obtain ⟨θ, hθ, x, hx, e⟩ := Submodule.mem_sup.1 (hP p.2)
    have e' : θ + x = D.sp.iXY 0 (p : (D.sp.X 0).V) := e
    have hx' : x ∈ F0.X := hx
    have h1 : θ - D.sp.iXY 0 (p : (D.sp.X 0).V) ∈ F0.X := by
      rw [← e']; simpa using hx'
    refine ⟨θ - D.sp.iXY 0 (p : (D.sp.X 0).V),
      ⟨Λ.sub_mem hθ.1 (iXY_mem_of_split D F0 he hs _ hθ.1 h1), h1⟩, fun b => ?_⟩
    rw [add_sub_cancel]
    exact orth_frame_of_mem_Thp hl hE hθ b
  choose f hf1 hf2 using ex
  have uniq : ∀ x ∈ F0.X, (∀ b, (hS D).hT x (frame F' b) = 0) → x = 0 := fun x hx h =>
    eq_zero_of_orth_frame (lf D F0) F' b₀ (by rw [hZ]; exact hb) hx h
  have hfX : ∀ p, f p ∈ F0.X := fun p => (hf1 p).2
  refine ⟨⟨⟨f, fun p q => ?_⟩, fun c p => ?_⟩, hf1, hf2⟩
  · rw [← sub_eq_zero]
    refine uniq _ (F0.X.sub_mem (hfX _) (F0.X.add_mem (hfX _) (hfX _))) fun b => ?_
    have h1 := hf2 (p + q) b
    have h2 := hf2 p b
    have h3 := hf2 q b
    simp only [Submodule.coe_add, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 h2 h3 ⊢
    linear_combination h1 - h2 - h3
  · show f (c • p) = c • f p
    have e1 : c • f p = algebraMap _ D.host.E c • f p := (algebraMap_smul D.host.E c (f p)).symm
    have e2 : ((c • p : P) : (D.sp.X 0).V) = algebraMap _ D.host.E c • (p : (D.sp.X 0).V) :=
      (algebraMap_smul D.host.E c (p : (D.sp.X 0).V)).symm
    rw [e1, ← sub_eq_zero]
    refine uniq _ (F0.X.sub_mem (hfX _) (F0.X.smul_mem _ (hfX _))) fun b => ?_
    have h1 := hf2 (c • p) b
    have h2 := hf2 p b
    rw [e2] at h1
    simp only [map_add, map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination h1 - (starRingEnd D.host.E) (algebraMap _ D.host.E c) * h2

theorem cntCl_ExSet_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  intro D u u' F0 Λ hst hb hrow hsp P Z s De Q hs1 hsk hsub hQ
  obtain ⟨reps, hcard, hreps, hall⟩ := GlobalTheory.T.exists_sublattice_lifts_modulo_fixing_unipotent D u u' F0 Λ hst hb hrow hsp P s De hsub
  obtain ⟨b₀, hb₀, -⟩ := hQ.2.2.1
  have h1 := cntCl_le_sum (TEqv_equivalence D Λ (lf D F0) (T' := ((Tu D u' : ℕ) : D.host.E))) reps
    (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P)
    (fun φ => FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (by
      intro F' hF'
      obtain ⟨φ, hφ, hφ'⟩ := exists_lift D F0 hb.1 hsp P Z b₀ hb₀ hF'
      obtain ⟨φ₀, h₀, n, ⟨hn, hnf⟩, hnp⟩ := hall φ hφ
      obtain ⟨hl, hE, hZ, -⟩ := hF'
      refine ⟨φ₀, h₀, moveFl n hn.1.1 F', ⟨⟨(aut_mem_iff hn.1 _).2 hl.1, rfl⟩,
        fun a => (aut_mem_iff hn.1 _).2 (hE a), ?_, fun p b => ?_⟩, n, hn, 1,
        fun a b h => Matrix.one_apply_ne h.ne', fun a => by simp, ?_⟩
      · rw [← hZ]
        funext a b
        change (hS D).hT (frame (lf D F0) a) (frame (moveFl n hn.1.1 F') b) =
          (hS D).hT (frame (lf D F0) a) (frame F' b)
        rw [frame_moveFl, ← hn.1.1 (frame (lf D F0) a) (frame F' b), hnf]
      · rw [frame_moveFl, ← hnp, hn.1.1]
        exact hφ' p b
      · rw [frameAct_one]
        funext b
        exact frame_moveFl _ _ _ b)
  have h2 : (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      ∑ φ ∈ reps, (cntCl (FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (TEqv D Λ (lf D F0)) : ℝ≥0∞) := by
    have := ENat.toENNReal_le.2 h1
    refine this.trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun φ hφ =>
    GlobalTheory.T.card_integral_frames_fixed_lift_le D u u' F0 Λ hst hb hrow hsp P φ Z s De Q hs1 hsk (hreps φ hφ) hsub hQ).trans ?_)
  have hnn : 0 ≤ NT D u ^ (2 * D.R.rS) * De ^ D.R.rS := le_trans (Nat.cast_nonneg _) hcard
  rw [frB, ENNReal.ofReal_mul hnn, nsmul_eq_mul]
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hcard

end GlobalTheory.LoopC.FrEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DsigWSubAvg
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_sub_avg {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} {v : H}
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD' : ∀ (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X →
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0) :
    ∀ D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) →
      Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (v - ∫ g, φ g • σ g v ∂μ) =
        Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D v - ∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ := by
  intro D
  induction D with
  | nil => intro _; rfl
  | cons X D ih =>
    intro hD
    have hX : Formalism.MainNotions.S.InLieHpk k r X := hD X List.mem_cons_self
    have hD1 : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y := fun Y hY => hD Y (List.mem_cons_of_mem _ hY)
    show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D _)) 0 = _
    rw [ih hD1]
    simp only [map_sub]
    exact ((Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU hv D hD1 hX).sub (hD' D X hD1 hX)).deriv

theorem kDense : Formalism.MainNotions.S.Pv.AmpDD.KDense := by
  intro k r ε lam H _ _ _ σ _ hDS v hv Ws hWs e he
  obtain ⟨-, hU, -⟩ := GlobalTheory.BesselMapOne.rep_of_isDSHpk hDS
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian k r
  have hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v := hv
  obtain ⟨hpc, hp1, hp01, hpδ⟩ := GlobalTheory.T.unitaryRealTraceBump_peak_properties (2 * r + k + 1) (Nat.succ_pos _)
  have hKc : IsCompact (GlobalTheory.ThA.KH k r) := isCompact_KH k r
  have hK1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r :=
    ⟨by show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * _ * 1 = _; simp,
      one_mem _⟩
  have hpK : ∀ x ∈ GlobalTheory.ThA.KH k r, 0 ≤ peak (2 * r + k + 1) x ∧ peak (2 * r + k + 1) x ≤ 1 :=
    fun x hx => hp01 x hx.2
  have hpU : ∀ U ∈ 𝓝 (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), ∃ δ < 1,
      ∀ x ∈ GlobalTheory.ThA.KH k r, x ∉ U → peak (2 * r + k + 1) x ≤ δ := fun U hU' => by
    obtain ⟨δ, hδ, h⟩ := hpδ U hU'
    exact ⟨δ, hδ, fun x hx hxU => h x hx.2 hxU⟩
  have hσ1 : σ 1 = 1 := hU.1.1
  have hconv : ∀ w ∈ Ws, Tendsto (fun m : ℕ => ∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
      atTop (𝓝 (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)) := by
    intro w hw
    have hc := (Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hU hv' w (hWs w hw)).mono
      (Set.inter_subset_left : GlobalTheory.ThA.KH k r ⊆ _)
    have := GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak _ μ hμ.1 _ 1 _ hKc hμ.2.1 hK1 hμ.2.2.2 hpc hp1 hpK hpU H _ hc
    rw [hσ1, ContinuousLinearMap.one_apply] at this
    exact this
  set L := Ws.length
  have hε : 0 < e / (L + 1) := by positivity
  have hev : ∀ᶠ m : ℕ in atTop, ∀ w ∈ {w | w ∈ Ws},
      dist (∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
        (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) < e / (L + 1) :=
    (Filter.eventually_all_finite Ws.finite_toSet).2 fun w hw => Metric.tendsto_nhds.1 (hconv w hw) _ hε
  obtain ⟨m, hm⟩ := hev.exists
  obtain ⟨N, b, c, hbc, hpoly, htr⟩ := GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys (2 * r + k + 1) m
  set Z : ℝ := ∫ h, peak (2 * r + k + 1) h ^ m ∂μ
  have e1 : ∀ g, peakN μ m g = ∑ j, (c j / (Z : ℂ)) * b j g := fun g => by
    show ((peak (2 * r + k + 1) g ^ m / Z : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, hpoly g, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∫ g, peakN μ m g • σ g v ∂μ, ?_, ?_⟩
  · have := GlobalTheory.T.integral_translate_family_isKFinite_hermitian k r H σ μ hU hμ N b hbc htr (fun j => c j / (Z : ℂ)) v
    simpa only [← e1] using this
  · have hD' := fun D X hD hX => GlobalTheory.T.hasDerivAt_derived_action_max_compact_average k r H σ μ (peakN μ m) v D X hU hμ
      (by rw [show peakN μ m = fun g => ∑ j, (c j / (Z : ℂ)) * b j g from funext e1]
          exact continuous_finset_sum _ fun j _ => continuous_const.mul (hbc j)) hv' hD hX
    have hterm : ∀ w ∈ Ws, ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖ ≤ e / (L + 1) := by
      intro w hw
      rw [Formalism.MainNotions.BridgeCS3d.dsigW_eq, dsigW_sub_avg hU hv' hD' w (hWs w hw), norm_sub_rev, ← dist_eq_norm]
      exact (hm w hw).le
    calc (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖).sum
        ≤ (Ws.map fun _ => e / (L + 1)).sum := List.sum_le_sum (fun w hw => hterm w hw)
      _ = L * (e / (L + 1)) := by simp [L, List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end GlobalTheory.KFinAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluation
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.EvalBound

theorem exists_contRep_bound_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  intro B d hB hL hn hg
  obtain ⟨F, hF, hc, hw⟩ := GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf B d hB hL 0 _ (tens_mem_VP B d hB)
  have he := GlobalTheory.StepAverage.isClosedEmbedding_entries_inf B.I
  have hσ : IsURep B.σs := (GlobalTheory.Dec.tensorRep B d hB).1
  obtain ⟨-, -, hN, hC, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  let a : B.I.Ginf → ℂ := fun g => F fun v i j => uMat (g v) i j
  have hs : SmoothInf B.I a := fun x => ⟨F, hF.contDiffAt, Filter.Eventually.of_forall fun _ => rfl⟩
  have hac : HasCompactSupport a := hc.comp_isClosedEmbedding he
  have hai : Integrable a (muInf B.I) := by
    unfold muInf
    exact (hF.continuous.comp he.continuous).integrable_of_hasCompactSupport hac
  obtain ⟨T, hT1, hT2⟩ := GlobalTheory.absOpInt B.I.Ginf (muInf B.I) _ (realRep B) (fun g x => hN _ x)
    (fun x => (hC x).comp (continuous_id.prodMk continuous_const)) a hai
  obtain ⟨C, hC⟩ := GlobalTheory.SmoothGrowth.convolutionSmoothL2 B B.g hn hg a hs hac
  refine ⟨C, fun A hA hk => ?_⟩
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := hC _ hk T ⟨hai, hT2⟩
  have hfix : T (A (B.tens B.w)) = A (B.tens B.w) := by
    rw [hT1]
    conv_rhs => rw [hw]
    rw [← A.integral_comp_comm (GlobalTheory.StepAverage.integrable_inf B hσ _ hF.continuous hc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have h := congrArg (fun S => S (B.tens B.w)) (hA g)
    simp only [map_smul]
    exact congrArg (a g • ·) h.symm
  rw [hfix] at hf4
  exact ⟨f, ⟨hf2, hf1.1, hf4⟩, hf3⟩

end GlobalTheory.EvalBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStabiliserFromAdaptedPairStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerDatumStabiliser_from_adapted_pair : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (lam lam' Λ : LV D) (γ g h : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → (∀ σ, Adapt σ F0 F0 → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam) F0 = Lsub lam F0 → ∃ n ∈ NRat F0, Formalism.HermitianLatticesTheory.gmap (n * σ) lam = lam) → (∀ σ, Adapt σ F0' F0' → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam') F0' = Lsub lam' F0' → ∃ n ∈ NRat F0', Formalism.HermitianLatticesTheory.gmap (n * σ) lam' = lam') → h ∈ stabL F F' Λ → ∃ b, GlobalTheory.StabCnt.InB F0 F0' lam lam' γ b ∧ GlobalTheory.StabCnt.Corr F0 F F0' F' γ g b h := by
  first | exact @GlobalTheory.StabCnt.stab_onto | exact GlobalTheory.StabCnt.stab_onto | (intros; apply GlobalTheory.StabCnt.stab_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeAutomorphismsEqAdaptedModUnipotentStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u, ∃ A N : Subgroup (GV D), (A : Set (GV D)) = Aut0 (lf D (X.Fu u)) Λ ∧ (N : Set (GV D)) = NLam Λ (lf D (X.Fu u)) ∧ N ≤ A ∧ (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) ∧ N.relIndex A = Nat.card (autLz D (X.Fu u) Λ) ∧ 0 < Nat.card (autLz D (X.Fu u) Λ) := by
  first | exact @GlobalTheory.AutQuot.autQuot | exact GlobalTheory.AutQuot.autQuot | (intros; apply GlobalTheory.AutQuot.autQuot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRowsStatement
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowMap_surjective_of_primitiveRows : ∀ (D : D7) [IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.rowMap_surjective_of_primitiveRows_alt | exact GlobalTheory.rowMap_surjective_of_primitiveRows_alt | (intros; apply GlobalTheory.rowMap_surjective_of_primitiveRows_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
section
namespace GlobalTheory

theorem rowsFinDim_link : Formalism.L2.SG.RowsDef.RowsFinDim :=
  CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsSpanAdelicLatticeModLevel
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameSpan

theorem span_mod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ x, p (embA X wt ιA x) = embA X wt ιA x) → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → ∀ y ∈ hat D.host.F (Mq wt), InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  intro D X u wt ιA hW hI c p hc hp hpL hef hz b bd hb hbd y hy
  have h1 := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI).1
  have hv : embA X wt ιA y ∈ X.B.I.Lf := (h1 y).1 hy
  have hA := GlobalTheory.T.moved_type_vectors_span_fixed_lattice_vector_mod_level D X u c p hc hpL hef hz _ hv (hp y)
  have e1 : (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i))) =
      Set.range (fun i => embA X wt ιA (b i)) := by
    congr 1; funext i; exact (hb i).symm
  have e2 : (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) =
      Set.range (fun i => embA X wt ιA (bd i)) := by
    congr 1; funext i; exact (hbd i).symm
  rw [e1, e2] at hA
  exact GlobalTheory.T.adelic_embedding_basis_lies_in_module D X u wt ιA hW hI b bd y hA

end GlobalTheory.St.G.FrameSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlaceStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_integration_formula_real_place : IwasawaFormula := by
  first | exact @GlobalTheory.FlagMeas.iwasawaFormula | exact GlobalTheory.FlagMeas.iwasawaFormula | (intros; apply GlobalTheory.FlagMeas.iwasawaFormula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegralityStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordFrame_dualTuple_gram_integrality : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧ GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧ GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  first | exact @GlobalTheory.CovDom.frame_dual_lat | exact GlobalTheory.CovDom.frame_dual_lat | (intros; apply GlobalTheory.CovDom.frame_dual_lat <;> assumption)
end

