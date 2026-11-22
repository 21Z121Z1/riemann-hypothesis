import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0211
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import CompanionTheory.AutomorphicTheory.RankOneTori.MatGroupOf

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameTermCountSublatticeBound
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrCount

open GlobalTheory.LoopC.FrEqv

theorem cntCl_le_of_map {α β : Type} {R : α → α → Prop} {R' : β → β → Prop} (hR : Equivalence R)
    (hR' : Equivalence R') (X : Set α) (Y : Set β) (φ : α → β)
    (h1 : ∀ a ∈ X, ∃ c, R a c ∧ φ c ∈ Y) (h2 : ∀ c c', R' (φ c) (φ c') → R c c') :
    cntCl X R ≤ cntCl Y R' := by
  rw [cntCl_eq_encard hR, cntCl_eq_encard hR']
  refine le_trans (Set.encard_le_encard ?_)
    (Set.encard_image_le (fun C : Set β => {d | ∃ c, φ c ∈ C ∧ R c d}) _)
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨c, hc, hY⟩ := h1 a ha
  refine ⟨_, ⟨φ c, hY, rfl⟩, ?_⟩
  ext d
  constructor
  · rintro ⟨c', h3, h4⟩
    exact hR.trans hc (hR.trans (h2 c c' h3) h4)
  · intro hd
    exact ⟨c, hR'.refl _, hR.trans (hR.symm hc) hd⟩

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def mapFlag (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (G : LFlag S r T') : LFlag S r T' where
  fl :=
    { e := fun a => n (G.fl.e a)
      z := n G.fl.z
      e_indep := G.fl.e_indep.map' (n : S.V →ₗ[E] S.V) (LinearEquiv.ker n)
      e_iso := fun a b => (hn _ _).trans (G.fl.e_iso a b)
      z_orth := fun a => (hn _ _).trans (G.fl.z_orth a)
      z_norm := (hn _ _).trans G.fl.z_norm }
  zt := n G.zt

theorem frame_mapFlag (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (G : LFlag S r T') (b : Fin (r + 1)) :
    frame (mapFlag n hn G) b = n (frame G b) := by
  refine Fin.lastCases ?_ (fun i => ?_) b
  · simp [frame, FlagG.fvec, mapFlag]
  · simp [frame, FlagG.fvec, mapFlag]

theorem symm_mem_X_mapFlag (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (G : LFlag S r T') {y : S.V}
    (hy : y ∈ Xsp (mapFlag n hn G)) : n.symm y ∈ Xsp G := by
  have : Xsp (mapFlag n hn G) ≤ (Xsp G).comap (n.symm : S.V →ₗ[E] S.V) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    change n.symm (n (G.fl.e a)) ∈ Xsp G
    rw [n.symm_apply_apply]
    exact Submodule.subset_span ⟨a, rfl⟩
  exact this hy

theorem fix_X {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hf : ∀ b, n (frame F b) = frame F b) {x : S.V}
    (hx : x ∈ Xsp F) : n x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have := hf a.castSucc
    simpa [frame, FlagG.fvec] using this
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem isometry_fix_flagAnisotropicVector_of_fix_frame {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hf : ∀ b, n (frame F b) = frame F b) :
    n F.fl.z = F.fl.z := by
  have := hf (Fin.last _)
  simpa [frame, FlagG.fvec] using this

theorem symm_fix {n : S.V ≃ₗ[E] S.V} {x : S.V} (h : n x = x) : n.symm x = x := by
  conv_lhs => rw [← h]
  simp

theorem Xflag_le_X (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem mem_orth' {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem ap_mem_gmap {Λ : Submodule (𝓞 E) S.V} (n : S.V ≃ₗ[E] S.V) (x : S.V) :
    n x ∈ Formalism.HermitianLatticesTheory.gmap n Λ ↔ x ∈ Λ := by
  rw [mem_gmap, n.symm_apply_apply]

theorem Lsub_gmap {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (Λ : Submodule (𝓞 E) S.V)
    (ho : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) : Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  unfold Lsub
  congr 1
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨h1, h2⟩
    have h3 : n.symm y - y ∈ Xsp F := symm_sub_mem n X_le_orth ho y h2
    have h4 : n.symm y ∈ orth S (Xsp F) := by
      simpa using (orth S (Xsp F)).add_mem (X_le_orth h3) h2
    have e : y = n.symm y - (n.symm y - y) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨(mem_gmap n y).1 h1, h4⟩) (Submodule.mem_sup_right h3)
  · refine sup_le ?_ le_sup_right
    rintro y ⟨h1, h2⟩
    have h3 : n y - y ∈ Xsp F := ho y h2
    have h4 : n y ∈ orth S (Xsp F) := by
      simpa using (orth S (Xsp F)).add_mem (X_le_orth h3) h2
    have e : y = n y - (n y - y) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨(ap_mem_gmap n y).2 h1, h4⟩) (Submodule.mem_sup_right h3)

theorem conj_mem_NLam {F : LFlag S r T} {n m : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b)
    (ho : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) (hm : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap n Λ) F) :
    n.symm * (m * n) ∈ NLam Λ F := by
  refine ⟨⟨mul_mem (inv_mem hn) (mul_mem hm.1.1 hn), ?_⟩, fun j x hx => ?_, ?_⟩
  · ext x
    rw [mem_gmap, ← ap_mem_gmap n, ← aut_mem_iff hm.1, mem_gmap]
    change (n.symm * (m * n)) ((n.symm * (m * n)).symm x) ∈ Λ ↔ _
    simp
  · have h1 : n x = x := fix_X hf (Xflag_le_X F _ hx)
    have h2 := hm.2.1 j x hx
    have h3 : m x ∈ Xsp F := by
      simpa using (Xsp F).add_mem (Xflag_le_X F _ h2) (Xflag_le_X F _ hx)
    change n.symm (m (n x)) - x ∈ _
    rw [h1, symm_fix (fix_X hf h3)]
    exact h2
  · exact trans_sub_mem _ _ X_le_orth (trans_sub_mem _ _ X_le_orth ho hm.2.2) (symm_sub_mem n X_le_orth ho)

theorem X_le_UUE {F : LFlag S r T} (G : LFlag S r T') {Λ : Submodule (𝓞 E) S.V}
    (hΛ : Submodule.span E (Λ : Set S.V) = ⊤) : Xsp F ≤ UUE Λ F G := by
  intro x hx
  have h0 : x ∈ Submodule.span E (Λ : Set S.V) := hΛ ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ x h0
  rw [Submodule.span_eq] at ht
  have h1 : (t : 𝓞 E) • x ∈ UU Λ F G :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      ⟨ht, (toO S (Xsp F)).smul_mem (t : 𝓞 E) hx⟩))
  have h2 : ((t : 𝓞 E) : E) • x ∈ UUE Λ F G := by
    have : ((t : 𝓞 E) : E) • x = (t : 𝓞 E) • x := algebraMap_smul E (t : 𝓞 E) x
    rw [this]
    exact Submodule.subset_span h1
  have h3 : ((t : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero t.2
    exact_mod_cast this
  exact (Submodule.smul_mem_iff _ h3).1 h2

theorem Thp_map {F : LFlag S r T} (G : LFlag S r T') {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b) (hz : F.zt = F.fl.z) {t : S.V}
    (ht : t ∈ Thp Λ F G) : n t ∈ Thp (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) := by
  refine ⟨(ap_mem_gmap n t).2 ht.1, ?_⟩
  have key : UUE (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) ≤ (UUE Λ F G).comap (n.symm : S.V →ₗ[E] S.V) := by
    refine Submodule.span_le.mpr ?_
    have : UU (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) ≤ Formalism.HermitianLatticesTheory.gmap n (UU Λ F G) := by
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · rintro y ⟨h1, h2⟩
        rw [mem_gmap]
        refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
          ⟨(mem_gmap n y).1 h1, ?_⟩))
        rw [symm_fix (fix_X hf h2)]
        exact h2
      · refine Submodule.span_le.mpr ?_
        rintro _ rfl
        change F.zt ∈ Formalism.HermitianLatticesTheory.gmap n (UU Λ F G)
        rw [mem_gmap, symm_fix (show n F.zt = F.zt by rw [hz]; exact isometry_fix_flagAnisotropicVector_of_fix_frame hf)]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.mem_span_singleton_self _)))
      · rintro y ⟨h1, h2⟩
        rw [mem_gmap]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right
          ⟨(mem_gmap n y).1 h1, symm_mem_X_mapFlag n hn G h2⟩)
      · refine Submodule.span_le.mpr ?_
        rintro _ rfl
        change n G.zt ∈ Formalism.HermitianLatticesTheory.gmap n (UU Λ F G)
        rw [ap_mem_gmap]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    intro y hy
    exact Submodule.subset_span ((mem_gmap n y).1 (this hy))
  change n t ∈ orth S _
  rw [mem_orth']
  intro x hx
  have h1 := (mem_orth'.1 ht.2) _ (key hx)
  have h2 := hn (n.symm x) t
  rw [n.apply_symm_apply] at h2
  exact h2.trans h1

theorem Thp_sup_le {F : LFlag S r T} (G : LFlag S r T') {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (hΛ : Submodule.span E (Λ : Set S.V) = ⊤)
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b)
    (ho : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) (hz : F.zt = F.fl.z) :
    Thp Λ F G ⊔ toO S (Xsp F) ≤ Thp (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) ⊔ toO S (Xsp F) := by
  refine sup_le ?_ le_sup_right
  intro t ht
  have h1 : t ∈ orth S (Xsp F) := mem_orth'.2 fun x hx => mem_orth'.1 ht.2 x (X_le_UUE G hΛ hx)
  have e : t = n t - (n t - t) := by abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Thp_map G hn hf hz ht)) (Submodule.mem_sup_right (ho t h1))

theorem Zhat_mapFlag {F : LFlag S r T} (G : LFlag S r T') {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b) :
    ZhatL F (mapFlag n hn G) = ZhatL F G := by
  funext a b
  change S.hT (frame F a) (frame (mapFlag n hn G) b) = S.hT (frame F a) (frame G b)
  rw [frame_mapFlag, ← hn (frame F a) (frame G b), hf]

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntFr D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  intro D u u' F0 Λ hS hB hR P Z s De Q hs hk hP hQ
  obtain ⟨n, ⟨hn, hf, ho⟩, hsp, hR'⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ hB hR hS.2.1.one_lt.le
  have hL : L0X D (Formalism.HermitianLatticesTheory.gmap n Λ) (lf D F0) = L0X D Λ (lf D F0) := by
    unfold L0X L0sub
    rw [Lsub_gmap Λ ho]
  refine le_trans ?_ (GlobalTheory.T.card_exactGramIntegralFrameClasses_le D u u' F0 _ hS hB hR' hsp P Z s De Q hs hk (hL ▸ hP) hQ)
  refine ENat.toENNReal_le.2 ?_
  refine cntCl_le_of_map (TEqv_equivalence D Λ _) (TEqv_equivalence D _ _) _ _ (mapFlag n hn) ?_ ?_
  · intro a ha
    obtain ⟨c, ⟨c1, c2, c3, c4⟩, hc⟩ := GlobalTheory.T.exists_exactGram_frame_in_termClass D u u' F0 Λ hS hB hR P Z a ha
    refine ⟨c, hc, ⟨(ap_mem_gmap n _).2 c1.1, congrArg n c1.2⟩, fun a => (ap_mem_gmap n _).2 (c2 a),
      (Zhat_mapFlag c hn hf).trans c3, c4.trans ?_⟩
    exact Submodule.comap_mono (Thp_sup_le c hR.2.1.1.span_eq_top hn hf ho rfl)
  · rintro c c' ⟨m, hm, ξ, h1, h2, h3⟩
    refine ⟨_, conj_mem_NLam hn hf ho hm, ξ, h1, h2, ?_⟩
    have h4 := map_frameAct n.symm (fun a => m (frame (mapFlag n hn c) a)) ξ
    rw [← h3] at h4
    simp only [frame_mapFlag, LinearEquiv.symm_apply_apply] at h4
    exact h4

end GlobalTheory.LoopC.FrCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselPairMajorantMulRight
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.CellMajTransfer

open Formalism.FourierDecayAlt in

theorem pt_bound {k r : ℕ} (L : LocBessel k r) {γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ₁ ∈ UH (Hpk k r)) (ha : a ∈ UH (Hpk k r)) {b : ℝ} (hb : 0 ≤ b) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ h ∈ UWset k r L.z', B.gN h ≤ K)
    {p : PairSp k r} (hp : p ∈ GlobalTheory.CellOrbInt.pairSet L) {h'' : Mt k r} (hh : Matrix.of h'' ∈ UWset k r L.z') :
    pairMaj (γ₁ * a) b p ≤ (K * K * B.gN a⁻¹) ^ b * pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set X : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * (γ₁ * a) *
    Matrix.of p.2.2 * Matrix.of p.2.1 with hX
  set Y : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ₁ *
    (a * Matrix.of p.2.2 * a⁻¹) * Matrix.of h'' with hY
  have hXv : pairMaj (γ₁ * a) b p = B.gN X ^ (-b) := rfl
  have hYv : pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) = B.gN Y ^ (-b) := rfl
  rw [hXv, hYv]
  have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
  have eY : Y = X * ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := by
    simp only [hX, hY, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hh'u]
  have hai : a⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha
  have hA1 : 1 ≤ B.gN a⁻¹ := P.BetaSesquilinearity.gN_ge_one hai
  have hYG : Y ∈ B.GV k r := by
    rw [hY]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1)) hγ)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul ha h4.1) hai)) hh.1
  have hY1 : 1 ≤ B.gN Y := P.BetaSesquilinearity.gN_ge_one hYG
  have hX0 : 0 ≤ B.gN X := P.B6.gN_nonneg X
  have hle : B.gN Y ≤ (K * K * B.gN a⁻¹) * B.gN X := by
    rw [eY]
    have e1 := P.B6.gN_mul_le X ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have e2 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) (Matrix.of h'')
    have e3 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹) a⁻¹
    have k1 := hK _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
    have k2 := hK _ hh
    have n1 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹)
    have n2 := P.B6.gN_nonneg (a⁻¹)
    have n3 := P.B6.gN_nonneg (Matrix.of h'' : B.Mat k r)
    have n4 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹)
    have n5 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have s1 : B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') ≤ K * K * B.gN a⁻¹ := by
      calc _ ≤ B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) * B.gN (Matrix.of h'' : B.Mat k r) := e2
        _ ≤ (B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹) * B.gN a⁻¹) * K :=
            mul_le_mul e3 k2 n3 (mul_nonneg n1 n2)
        _ ≤ (K * B.gN a⁻¹) * K := by gcongr
        _ = K * K * B.gN a⁻¹ := by ring
    calc _ ≤ B.gN X * B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := e1
      _ ≤ B.gN X * (K * K * B.gN a⁻¹) := mul_le_mul_of_nonneg_left s1 hX0
      _ = (K * K * B.gN a⁻¹) * B.gN X := by ring
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hc0 : 0 < c := by linarith
  have hcb : c ^ b * c ^ (-b) = 1 := by
    rw [← Real.rpow_add hc0, add_neg_cancel, Real.rpow_zero]
  have hmono : (c * B.gN X) ^ (-b) ≤ B.gN Y ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
  calc B.gN X ^ (-b) = c ^ b * (c * B.gN X) ^ (-b) := by
        rw [Real.mul_rpow hc0.le hX0, ← mul_assoc, hcb, one_mul]
    _ ≤ c ^ b * B.gN Y ^ (-b) := mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hc0.le _)

end GlobalTheory.CellMajTransfer

namespace GlobalTheory.CellMajTransfer

open Formalism.FourierDecayAlt in

theorem inner_eq {k r : ℕ} (L : LocBessel k r) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {C : ℝ≥0∞}
    (hmap : L.μN.map (conjM a) = C • L.μN) {f : PairSp k r → ℝ≥0∞} (hfm : Measurable f) (x : Mt k r × Mt k r) :
    ∫⁻ y, ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' ∂(L.μW'.prod L.μN) = C * ∫⁻ y, f (x, y) ∂(L.μW'.prod L.μN) := by
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hF : Measurable fun q : Mt k r × (Mt k r × Mt k r) => f (x, (q.1, conjM a q.2.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk (hconj.comp measurable_snd.snd)))
  have hG : Measurable fun y : Mt k r × Mt k r => ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' :=
    hF.lintegral_prod_left'
  have hH' : Measurable fun q : Mt k r × Mt k r => f (x, (q.1, q.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hH : Measurable fun n' : Mt k r => ∫⁻ h'', f (x, (h'', n')) ∂L.μW' := hH'.lintegral_prod_left'
  have hfx : Measurable fun y : Mt k r × Mt k r => f (x, y) := hfm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hG.aemeasurable, lintegral_prod _ hfx.aemeasurable]
  simp only [lintegral_const, L.hμW'.2, one_mul]
  have e1 : ∫⁻ n', ∫⁻ h'', f (x, (h'', conjM a n')) ∂L.μW' ∂L.μN =
      ∫⁻ n', ∫⁻ h'', f (x, (h'', n')) ∂L.μW' ∂(L.μN.map (conjM a)) := by
    rw [lintegral_map hH hconj]
  rw [e1, hmap, lintegral_smul_measure, smul_eq_mul]
  have hs := lintegral_lintegral_swap (μ := L.μW') (ν := L.μN) (f := fun h'' n' => f (x, (h'', n')))
    hH'.aemeasurable
  rw [hs, mul_one]

open Formalism.FourierDecayAlt in

theorem integrable_mul_right : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (C : ℝ≥0∞), 0 < L.κN → L.κN ≠ ⊤ → 0 ≤ b → γ₁ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → C ≠ ⊤ → L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ₁ b) (Formalism.MainNotions.S.pairMeas L) → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (γ₁ * a) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L γ₁ a b C _hκ0 _hκ hb hγ ha hC hmap hint
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  obtain ⟨K, hK1, hK⟩ := P.Dx3.UW_bound L.z' L.hz'.1 L.hz'.2
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  set f : PairSp k r → ℝ≥0∞ := fun p => ENNReal.ofReal (pairMaj γ₁ b p) with hfdef
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (GlobalTheory.CellMaj.meas_pairMaj γ₁ b)
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  set Φ : PairSp k r × Mt k r → PairSp k r := fun q => (q.1.1, (q.2, conjM a q.1.2.2)) with hΦdef
  have hΦ : Measurable Φ := measurable_fst.fst.prodMk (measurable_snd.prodMk (hconj.comp measurable_fst.snd.snd))
  have aW' : ∀ᵐ y ∂L.μW', Matrix.of y ∈ UWset k r L.z' := by rw [ae_iff]; exact L.hμW'.1.2.2.1
  have hP0 : ∀ p, 0 ≤ pairMaj (γ₁ * a) b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hQ0 : ∀ p, 0 ≤ pairMaj γ₁ b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hcb0 : 0 ≤ c ^ b := Real.rpow_nonneg (by rw [hc]; have := P.B6.gN_nonneg a⁻¹; positivity) _
  have step1 : ∀ᵐ p ∂(pairMeas L), ENNReal.ofReal (pairMaj (γ₁ * a) b p) ≤
      ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' := by
    filter_upwards [GlobalTheory.CellOrbInt.ae_pairMeas L] with p hp
    calc ENNReal.ofReal (pairMaj (γ₁ * a) b p) = ∫⁻ _h'', ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂L.μW' := by
          rw [lintegral_const, L.hμW'.2, mul_one]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [aW'] with h'' hh
          rw [hfdef, ← ENNReal.ofReal_mul hcb0]
          exact ENNReal.ofReal_le_ofReal (pt_bound L hγ ha hb hK1 hK hp hh)
  have step2 : ∫⁻ p, ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) = C * ∫⁻ p, f p ∂(pairMeas L) := by
    have hm : Measurable fun p : PairSp k r => ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' := (hfm.comp hΦ).lintegral_prod_right'
    unfold pairMeas
    rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hfm.aemeasurable]
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_congr fun x => ?_
    exact inner_eq L a hmap hfm x
  have hfin : ∫⁻ p, f p ∂(pairMeas L) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hQ0)).1 hint.2
  refine ⟨(GlobalTheory.CellMaj.meas_pairMaj (γ₁ * a) b).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP0)]
  calc ∫⁻ p, ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂(pairMeas L)
      ≤ ∫⁻ p, ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) := lintegral_mono_ae step1
    _ = ENNReal.ofReal (c ^ b) * (C * ∫⁻ p, f p ∂(pairMeas L)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [step2]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hC.lt_top hfin)

end GlobalTheory.CellMajTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjUnipotentHaarEqSmul
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
namespace GlobalTheory.NConjHaar

theorem map_conj_eq_smul : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r), 0 < L.κN → L.κN ≠ ⊤ → ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ n, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ a * n * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN := by
  intro k r L h0 ht a ha hN
  have hμ := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN h0 ht.lt_top
  have hu : IsUnit a.det := GlobalTheory.Amp.StabHaar.unit_of_GG ha
  have hmap := GlobalTheory.Amp.StabHaar.haar_conj (G := Formalism.QuantumDeterminants.Nset k r) (G' := Formalism.QuantumDeterminants.Nset k r) a hu hN hμ
  obtain ⟨c, c0, ct, hc⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (Formalism.FourierDecayAlt.P.B2x2.closedN k r) hmap hμ
  exact ⟨c, ct, hc⟩

end GlobalTheory.NConjHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorant
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.CellPts

theorem cell_points : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), Formalism.MainNotions.S.ThB.Gpt (Formalism.QuantumDeterminants.Tz k r L.z) (Formalism.QuantumDeterminants.Tz k r L.z') γ ≠ 0 → Formalism.MainNotions.S.IsPtRep L γ g → Formalism.MainNotions.S.IsRelStab L g → Formalism.MainNotions.S.IsRootMeas L γ g μR → Formalism.MainNotions.S.IsOrbQuot L g μR ν → IsHaarOn (Formalism.MainNotions.S.RStab k r g) μR ∧ (∃ νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j)) νR) ∧ ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj g b) ν := by
  intro k r L h μG hO hC h1 h0 hc hμG γ g μR ν hG hrep hrel hroot hq
  have hR := Formalism.MainStatements.RankOne.root_haar hO.1 L hc hrep hroot
  have hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' g) :=
    ⟨Formalism.MainNotions.BigCellDensity.wPt γ, Formalism.MainNotions.BigCellDensity.dPt γ, Formalism.MainNotions.BigCellDensity.dPt_ne γ, by
      rw [hrep.2, ← Formalism.MainNotions.BigCellDensity.ptMatN_swap, Formalism.MainNotions.BigCellDensity.ptMatN_mono]⟩
  have hpos : 0 < Gf k r L.z L.z' g := by
    refine lt_of_le_of_ne (gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g hrep.1) fun e => hG ?_
    rw [← Formalism.MainNotions.BigCellDensity.gTie k r L.z L.z' γ g hrep.1 hrep.2, ← e]
  obtain ⟨νR, hν⟩ := Formalism.MainStatements.RankOne.quot_exists hrep.1 hμG hR
  refine ⟨hR, ⟨νR, hν⟩, ?_⟩
  exact GlobalTheory.CellMaj.cellConv k r L h μG g μR νR ν h1 hO hC ⟨hrep.1, hpos, hmono, hrel, hR, hq, hν⟩ hmono

end GlobalTheory.CellPts
end

