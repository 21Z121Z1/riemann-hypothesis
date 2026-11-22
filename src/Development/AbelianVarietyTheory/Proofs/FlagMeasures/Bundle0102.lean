import Mathlib
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairExistsUnipotentSplitLattice
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.SplitLift

section Lattice

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (M : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem exists_split (Λ : Submodule R V) (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set V) = ⊤)
    (S I : Submodule K V) :
    ∃ W : Submodule K V, W ≤ S ∧ W ⊓ I = ⊥ ∧ S ≤ W ⊔ I ∧
      ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ W ∧ l - w ∈ I := by
  set M : Submodule R V := Λ ⊓ S.restrictScalars R with hM
  have hMfg : M.FG := by
    haveI : Module.Finite R Λ := Module.Finite.iff_fg.2 hfg
    exact (Module.Finite.iff_fg (N := M)).1
      (Module.Finite.of_injective (Submodule.inclusion (inf_le_left : M ≤ Λ))
        (Submodule.inclusion_injective _))
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 hMfg
  let π : M →ₗ[R] (V ⧸ I) := (I.mkQ.restrictScalars R) ∘ₗ M.subtype
  haveI : Module.IsTorsionFree R (V ⧸ I) := Module.IsTorsionFree.trans K
  haveI : Module.Finite R (LinearMap.range π) := inferInstance
  haveI : Module.Flat R (LinearMap.range π) := inferInstance
  haveI : Module.FinitePresentation R (LinearMap.range π) :=
    Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (LinearMap.range π) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π.rangeRestrict LinearMap.id
    π.surjective_rangeRestrict
  have hσ' : ∀ y, π (σ y) = (y : V ⧸ I) := fun y => by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  set N : Submodule R V := LinearMap.range (M.subtype ∘ₗ σ) with hN
  have key : ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ Submodule.span K (N : Set V) ∧ l - w ∈ I := by
    intro l hl hlS
    let y : LinearMap.range π := ⟨π ⟨l, hl, hlS⟩, _, rfl⟩
    refine ⟨(σ y : V), (σ y).2.1, Submodule.subset_span ⟨y, rfl⟩, ?_⟩
    rw [← Submodule.Quotient.eq]
    exact (hσ' y).symm
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R K d ≠ 0 := fun d hd =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd
  refine ⟨Submodule.span K (N : Set V), ?_, ?_, ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact (σ y).2.2
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxI⟩
    obtain ⟨d, hd, y, hy⟩ := exists_smul_mem N hx
    have hy' : ((σ y : M) : V) = d • x := hy
    have h0 : (y : V ⧸ I) = 0 := by
      rw [← hσ' y]
      show I.mkQ ((σ y : M) : V) = 0
      rw [hy', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.smul_of_tower_mem d hxI
    have h1 : y = 0 := Subtype.ext h0
    rw [h1, map_zero, ← algebraMap_smul K d x] at hy'
    exact (smul_eq_zero.1 hy'.symm).resolve_left (hinj d hd)
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) Λ (x := x) (by rw [hsp]; trivial)
    obtain ⟨w, -, hw, hwI⟩ := key _ hdx (S.smul_of_tower_mem d hx)
    have h1 : d • x ∈ Submodule.span K (N : Set V) ⊔ I :=
      Submodule.mem_sup.2 ⟨w, hw, _, hwI, by abel⟩
    rw [← algebraMap_smul K d x] at h1
    exact (Submodule.smul_mem_iff _ (hinj d hd)).1 h1

end Lattice

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

section Geometry
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem flip_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem mem_wSp_iff (F F' : FlagD H r) (w : V) : w ∈ wSp F F' ↔ ∀ y ∈ V0 F F', H.B y w = 0 := by
  rw [wSp, mem_perp_iff]
  exact ⟨fun h y hy => flip_zero (h y hy), fun h y hy => flip_zero (h y hy)⟩

theorem hermFlagPair_isotropic_sup_le_commonSpace (F F' : FlagD H r) : F.X ⊔ F'.X ≤ V0 F F' := le_sup_left

theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' :=
  (inf_le_left.trans le_sup_left).trans (hermFlagPair_isotropic_sup_le_commonSpace F F')

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b =>
    exact hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem X_perp (F : FlagD H r) {w x : V} (hw : ∀ a : Fin (r + 1), H.B (F.e a) w = 0) (hx : x ∈ F.X) :
    H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact hw _
  exact this hx

theorem aniso_right {F F' : FlagD H r} {j : ℕ} {hj : j ≤ r} {c : K} (h : NFFull F F' j hj c)
    (hF : F.Aniso) : F'.Aniso := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9⟩ := h
  intro w hw hww
  obtain ⟨x, hx, hwx⟩ := h9 w hw
  have h1 : H.B (w - x) (w - x) = 0 := by
    have a1 : H.B x (w - x) = 0 := hwx x (hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_right hx))
    have a2 : H.B w x = 0 := flip_zero (X_perp F' hw hx)
    rw [map_sub H.B, LinearMap.sub_apply, a1, map_sub, hww, a2]
    simp
  have h2 : w - x ∈ F.X := hF _ (fun a => hwx _ (flag_vector_mem_base_lattice F F' a)) h1
  have h3 : w - x ∈ F'.X := ((h6 _ h2).1 hwx).2
  simpa using add_mem h3 hx

end Geometry

theorem latTh_eq (F F' : FlagD H r) (hI : II F F' ≤ wSp F F') (Λ : Submodule (𝓞 K) V) :
    latTh F F' Λ = (Λ ⊓ rs (𝓞 K) (wSp F F')) ⊔ rs (𝓞 K) (II F F') := by
  have hu : ∀ y ∈ wSp F F', y ∈ uPerp F F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)
  have hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)
  apply le_antisymm
  · rintro y ⟨⟨hy1, -⟩, hy3⟩
    obtain ⟨l, ⟨hl, -⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩
    have : l + x - x ∈ wSp F F' := sub_mem hy3 (hI hx)
    simpa using this
  · refine sup_le ?_ ?_
    · rintro l ⟨hl, hw⟩
      exact ⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩
    · intro x hx
      exact ⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ
  obtain ⟨hfull, hlift, -, -, -, -, hw, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hL := (isLatMod_top_bot_iff Λ).1 hΛ.1.1.1
  obtain ⟨W, hWS, hWI, hSW, hWΛ⟩ :=
    exists_split Λ hL.fg hL.span_eq_top (wSp N.F N.F') (II N.F N.F')
  have hW : IsLift N.F N.F' W :=
    ⟨fun w h => (mem_wSp_iff _ _ w).1 (hWS h), hWI, fun w h => hSW ((mem_wSp_iff _ _ w).2 h)⟩
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hA : N.F.Aniso := by
    intro w h1 h2
    by_contra hne
    have := N.posdef σ w h1 hne
    rw [h2] at this
    simp at this
  obtain ⟨f, hf, hf', hfix, hmap⟩ := Formalism.HermitianLatticeCounting.P.complementLiftTransitive K V H r N.F N.F' W N.Wt
    ⟨1, by rw [star_one]; norm_num⟩ hA (aniso_right hfull hA) hW hlift
  let s : V ≃ₗ[K] V := LinearEquiv.ofBijective f hf.2.1
  refine ⟨s, Subgroup.subset_closure ⟨hf, hf'⟩, ?_⟩
  have hI : II N.F N.F' ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_right
  have hWt : N.Wt ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_left
  rw [NF.Split, latTh_eq _ _ hI]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy, hyw⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    have hlw : l ∈ wSp N.F N.F' := by
      refine (mem_wSp_iff _ _ l).2 fun y hy => ?_
      rw [← hf.1, hfix y hy]
      exact (mem_wSp_iff _ _ _).1 hyw y hy
    obtain ⟨w, hw1, hw2, hw3⟩ := hWΛ l hl hlw
    refine Submodule.mem_sup.2 ⟨f w, ⟨Submodule.smul_mem_pointwise_smul w s Λ hw1, ?_⟩, l - w, hw3, ?_⟩
    · show f w ∈ N.Wt
      rw [← hmap]
      exact ⟨w, hw2, rfl⟩
    · show f w + (l - w) = f l
      rw [← hfix _ (isotropicMeet_le_jointSpan _ _ hw3), map_sub]
      abel
  · exact sup_le_sup_right (inf_le_inf_left _ fun x hx => hWt hx) _

end GlobalTheory.DegCnt.SplitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotent
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def Cmp (H : HermSpace K V) (p q : V × V) : Prop := H.B p.1 q.1 = H.B p.2 q.2

theorem Cmp.symm {p q : V × V} (h : Cmp H p q) : Cmp H q p := by
  unfold Cmp at *
  rw [← H.herm, h, H.herm]

theorem cmp_span_left {S : Set (V × V)} {q : V × V} (h : ∀ p ∈ S, Cmp H p q) :
    ∀ p ∈ Submodule.span K S, Cmp H p q := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [Cmp]
  | add x y _ _ h1 h2 => simp only [Cmp] at *; simp [h1, h2]
  | smul a x _ h1 => simp only [Cmp] at *; simp [h1]

theorem exists_isometry (S : Set (V × V)) (h : ∀ p ∈ S, ∀ q ∈ S, Cmp H p q)
    (h1 : (Submodule.span K S).map (LinearMap.fst K V V) = ⊤)
    (h2 : (Submodule.span K S).map (LinearMap.snd K V V) = ⊤) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ ∀ p ∈ S, s p.1 = p.2 := by
  have hG : ∀ p ∈ Submodule.span K S, ∀ q ∈ Submodule.span K S, Cmp H p q := fun p hp q hq =>
    cmp_span_left (fun p hp => (cmp_span_left (fun q hq => h q hq p hp) q hq).symm) p hp
  set G := Submodule.span K S with hGdef
  have s1 : ∀ v : V, ∃ p : G, p.1.1 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h1.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have s2 : ∀ v : V, ∃ p : G, p.1.2 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h2.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have b1 : Function.Bijective ((LinearMap.fst K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s1⟩
    have e1 : p.1.1 = 0 := hp
    refine Subtype.ext (Prod.ext e1 (H.nondeg _ fun y => ?_))
    obtain ⟨q, rfl⟩ := s2 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this.symm
  have b2 : Function.Bijective ((LinearMap.snd K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s2⟩
    have e1 : p.1.2 = 0 := hp
    refine Subtype.ext (Prod.ext (H.nondeg _ fun y => ?_) e1)
    obtain ⟨q, rfl⟩ := s1 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this
  have key : ∀ p : G, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) p.1.1 = p.1.2 := by
    intro p
    have : (LinearEquiv.ofBijective _ b1).symm p.1.1 = p := (LinearEquiv.symm_apply_eq _).2 rfl
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨_, fun x y => ?_, fun p hp => key ⟨p, Submodule.subset_span hp⟩⟩
  obtain ⟨p, rfl⟩ := s1 x
  obtain ⟨q, rfl⟩ := s1 y
  rw [key, key]
  exact Eq.symm (hG _ p.2 _ q.2)

theorem gram_eq {F G : FlagD H r} (hT : F.T = G.T) (a b : Fin (r + 1)) :
    H.B (F.e a) (F.e b) = H.B (G.e a) (G.e b) := by
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · rw [F.zz, G.zz, hT]
  · rw [B_swap0 H (F.zperp b), B_swap0 H (G.zperp b)]
  · rw [F.zperp, G.zperp]
  · rw [F.iso, G.iso]

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_left F F') (fun a => isotropicSpan_le_jointSpan_left _ _ (e_mem_X _ a)) a

theorem hermFlag_secondFrame_mem_frameSpan (F F' : FlagD H r) (a : Fin (r + 1)) : F'.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_right F F') (fun a => isotropicSpan_le_jointSpan_right _ _ (e_mem_X _ a)) a

theorem perp_transfer {F G : FlagD H r} (h : SameGr F G) {w : V} (hw : ∀ a, H.B (F.e a) w = 0) (a : Fin (r + 1)) :
    H.B (G.e a) w = 0 := by
  have h1 := perp_X F (fun b => hw b.castSucc) _ (Xa_le_X F _ (h a))
  simpa [hw a] using h1

variable [NumberField K]

theorem wt_e (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (flag_vector_mem_base_lattice _ _ a))

theorem wt_e' (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F'.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (hermFlag_secondFrame_mem_frameSpan _ _ a))

theorem wt_ist (N : NF H r) {w : V} (hw : w ∈ N.Wt) (b : Fin r) (hb : N.j ≤ b.val) : H.B (N.ist b) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))

variable [FiniteDimensional K V]

theorem decomp (N : NF H r) {w : V} (hw : ∀ a, H.B (N.F.e a) w = 0) : ∃ w' ∈ N.Wt, w' - w ∈ N.F.X := by
  obtain ⟨x, hx, hp⟩ := (NFGeom.full N).2.2.2.2.2.2.2.1 w hw
  obtain ⟨u, hu, i, hi, e⟩ := Submodule.mem_sup.1 ((NFGeom.isLift N).2.2 _ hp)
  refine ⟨u, hu, ?_⟩
  have : u - w = -(x + i) := by rw [← sub_eq_zero, ← sub_eq_zero.2 e]; abel
  rw [this]
  exact Submodule.neg_mem _ (Submodule.add_mem _ hx hi.1)

theorem eq_top (N : NF H r) (M : Submodule K V) (h1 : ∀ a, N.F.e a ∈ M) (h2 : ∀ a, N.F'.e a ∈ M)
    (h3 : ∀ b : Fin r, N.j ≤ b.val → N.ist b ∈ M) (h4 : N.Wt ≤ M) : M = ⊤ := by
  rw [eq_top_iff, ← (NFGeom.isCompl N).sup_eq_top, NFGeom.Pi_eq]
  refine sup_le h4 (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) <;> refine Submodule.span_le.2 ?_
  · rintro _ ⟨b, -, rfl⟩; exact h1 _
  · rintro _ ⟨b, -, rfl⟩; exact h2 _
  · rintro _ (rfl | rfl)
    · exact h1 _
    · exact h2 _
  · rintro _ ⟨b, hb, rfl⟩; exact h3 b hb

theorem main (N₀ N₁ : NF H r) (h : SameGr N₀.F N₁.F) (hj : N₀.j = N₁.j) (hc : N₀.c = N₁.c) (hT : N₀.T = N₁.T)
    (hM : pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j) :
    ∃ s : V ≃ₗ[K] V, N₀.F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  have hX : N₁.F.X = N₀.F.X := AdaptInv.x_eq h
  have ee := gram_eq (F := N₀.F) (G := N₁.F) (by rw [N₀.hT, N₁.hT, hT])
  have e'e' := gram_eq (F := N₀.F') (G := N₁.F') (by rw [N₀.hT', N₁.hT', hT])
  have ee' : ∀ a b, H.B (N₀.F.e a) (N₀.F'.e b) = H.B (N₁.F.e a) (N₁.F'.e b) := by
    intro a b
    by_cases hb : N₀.j ≤ b.val
    · rw [N₀.same b hb, N₁.same b (hj ▸ hb)]
      simp [ee, hc]
    by_cases ha : N₀.j ≤ a.val
    · rw [NFGeom.e_eq N₀ a ha, NFGeom.e_eq N₁ a (hj ▸ ha)]
      simp [e'e', hc]
    have := congrFun (congrFun hM a) b
    simpa [pairM, ← hj, not_le.1 ha, not_le.1 hb] using this
  have ei : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F.e a) (N₀.ist b) = H.B (N₁.F.e a) (N₁.ist b) := by
    intro a b hb
    refine Fin.lastCases ?_ (fun a => ?_) a
    · exact (N₀.normalForm_dual_orthogonal_last b hb).trans (N₁.normalForm_dual_orthogonal_last b (hj ▸ hb)).symm
    · rw [N₀.ist_e a b hb, N₁.ist_e a b (hj ▸ hb)]
  have e'i : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F'.e a) (N₀.ist b) = H.B (N₁.F'.e a) (N₁.ist b) := by
    intro a b hb
    by_cases ha : N₀.j ≤ a.val
    · rw [N₀.same a ha, N₁.same a (hj ▸ ha)]
      simp [ei a b hb, hc]
    have hl : a.val < r := lt_of_lt_of_le (not_le.1 ha) N₀.j_le
    exact (N₀.ist_e' ⟨a.val, hl⟩ b (not_le.1 ha) hb).trans
      (N₁.ist_e' ⟨a.val, hl⟩ b (hj ▸ not_le.1 ha) (hj ▸ hb)).symm
  have ww : ∀ p q : V × V, p.1 ∈ N₀.Wt → q.1 ∈ N₀.Wt → p.2 - p.1 ∈ N₀.F.X → q.2 - q.1 ∈ N₀.F.X → Cmp H p q := by
    intro p q hp hq hp' hq'
    have a1 := perp_X N₀.F (fun b => wt_e N₀ hq b.castSucc) _ hp'
    have a2 := B_swap0 H (perp_X N₀.F (fun b => wt_e N₀ hp b.castSucc) _ hq')
    have a3 := X_iso N₀.F hp' hq'
    simp only [map_sub, LinearMap.sub_apply] at a1 a2 a3
    unfold Cmp
    linear_combination -a1 - a2 - a3
  obtain ⟨s, hs, hS⟩ := exists_isometry (H := H)
    {p | (∃ a, p = (N₀.F.e a, N₁.F.e a)) ∨ (∃ a, p = (N₀.F'.e a, N₁.F'.e a)) ∨
      (∃ b : Fin r, N₀.j ≤ b.val ∧ p = (N₀.ist b, N₁.ist b)) ∨ (p.1 ∈ N₀.Wt ∧ p.2 ∈ N₁.Wt ∧ p.2 - p.1 ∈ N₀.F.X)}
    (by
      rintro p (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨p0, p1, p2⟩) q (⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨q0, q1, q2⟩)
      · exact ee a b
      · exact ee' a b
      · exact ei a b hb
      · exact (wt_e N₀ q0 a).trans (wt_e N₁ q1 a).symm
      · exact Cmp.symm (ee' b a)
      · exact e'e' a b
      · exact e'i a b hb
      · exact (wt_e' N₀ q0 a).trans (wt_e' N₁ q1 a).symm
      · exact Cmp.symm (ei b a ha)
      · exact Cmp.symm (e'i b a ha)
      · exact (N₀.ist_iso a b ha hb).trans (N₁.ist_iso a b (hj ▸ ha) (hj ▸ hb)).symm
      · exact (wt_ist N₀ q0 a ha).trans (wt_ist N₁ q1 a (hj ▸ ha)).symm
      · exact Cmp.symm ((wt_e N₀ p0 b).trans (wt_e N₁ p1 b).symm)
      · exact Cmp.symm ((wt_e' N₀ p0 b).trans (wt_e' N₁ p1 b).symm)
      · exact Cmp.symm ((wt_ist N₀ p0 b hb).trans (wt_ist N₁ p1 b (hj ▸ hb)).symm)
      · exact ww p q p0 q0 p2 q2)
    (by
      refine eq_top N₀ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      exact ⟨(w, u), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), rfl⟩)
    (by
      refine eq_top N₁ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hj ▸ hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₀ (perp_transfer (AdaptInv.sameGr_symm h) (wt_e N₁ hw))
      exact ⟨(u, w), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hu, hw, by
        simpa using Submodule.neg_mem _ hx⟩))), rfl⟩)
  have se : ∀ a, s (N₀.F.e a) = N₁.F.e a := fun a => hS (_, _) (Or.inl ⟨a, rfl⟩)
  refine ⟨s, ⟨hs, s.bijective, fun a => ?_, fun y hy => ?_⟩,
    fun a => ⟨se a, hS (_, _) (Or.inr (Or.inl ⟨a, rfl⟩))⟩⟩
  · rw [LinearEquiv.coe_coe, se]
    exact h a.castSucc
  · let M : Submodule K V := N₀.F.X.comap ((s : V →ₗ[K] V) - LinearMap.id)
    have m1 : ∀ a, N₀.F.e a ∈ M := fun a => by
      change s (N₀.F.e a) - N₀.F.e a ∈ N₀.F.X
      rw [se]
      exact Xa_le_X _ _ (h a)
    have m2 : N₀.F.X ≤ M := Submodule.span_le.2 (by rintro _ ⟨b, -, rfl⟩; exact m1 _)
    have m3 : N₀.Wt ≤ M := fun w hw => by
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      change s w - w ∈ N₀.F.X
      rw [show s w = u from hS (w, u) (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), ← hX]
      exact hx
    obtain ⟨u, hu, hx⟩ := decomp N₀ (w := y + star (H.B N₀.F.z y / N₀.F.T) • N₀.F.z) (fun a => by
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have := N₀.F.hT
        change H.B N₀.F.z _ = 0
        simp only [map_add, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, pairing_lastVector_lastVector]
        field_simp
        ring
      · simp [hy a, pairing_isotropicSpan_lastVector N₀.F (e_mem_X _ a)])
    have m4 : y ∈ M := by
      have := M.sub_mem (M.sub_mem (m3 hu) (m2 hx))
        (M.smul_mem (star (H.B N₀.F.z y / N₀.F.T)) (m1 (Fin.last r)))
      simpa [FlagD.z] using this
    exact m4

end GlobalTheory.DegAsm.NFUnique

namespace GlobalTheory.DegAsm

theorem nf_unique : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  intro K V _ _ _ _ _ _ _ _ H _ r F N₀ N₁ h₀ h₁ hj hc hT hM
  have h : SameGr N₀.F N₁.F := fun a => by
    rw [AdaptInv.xa_eq h₀]
    simpa using Submodule.sub_mem _ (h₁ a) (h₀ a)
  obtain ⟨s, hs, he⟩ := NFUnique.main N₀ N₁ h hj hc hT hM
  exact ⟨s, AdaptInv.inN_of (AdaptInv.sameGr_symm h₀) _ hs, he⟩

end GlobalTheory.DegAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmulStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  first | exact @GlobalTheory.TripInv.trip_encard_smul | exact GlobalTheory.TripInv.trip_encard_smul | (intros; apply GlobalTheory.TripInv.trip_encard_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReferenceLatticeMemOfMemInnerSpanStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceLattice_mem_of_mem_innerSpan : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : GlobalTheory.DegCnt.NF H r) (L : Submodule (𝓞 K) V), N.F.z ∈ L → ∀ v ∈ N.Ref L, v ∈ N.Wn → v ∈ L := by
  first | exact @GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn | exact GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn | (intros; apply GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassBoundsStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_hermitianLattice_mass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ENNReal.ofReal (κ / 2 * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) ≤ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ∧ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ≤ ENNReal.ofReal (2 * κ * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) := by
  first | exact @GlobalTheory.HL.Unfold.mass_bounds | exact GlobalTheory.HL.Unfold.mass_bounds | (intros; apply GlobalTheory.HL.Unfold.mass_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedBlockAntidiagWithLeadingMinorsEncardLeStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedBlockAntidiag_with_leadingMinors_encard_le : ∀ (K : Type) [Field K] (j : ℕ) (δ : ℕ → K), (({P : Matrix (Fin j) (Fin j) K | (∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, P a b = w.mat a b * ((sgn b : ℤ) : K)) ∧ ∀ (l : ℕ) (hl : l ≤ j), (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = δ l}).encard : ℕ∞) ≤ 8 ^ j := by
  first | exact @GlobalTheory.signed_block_count | exact GlobalTheory.signed_block_count | (intros; apply GlobalTheory.signed_block_count <;> assumption)
end

