import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0126
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegUnram

open GlobalTheory.FamRep

theorem iso_up {Y Y' : Scheme.{0}} {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB)
    (hM' : M'.IsLB) (hN' : N'.IsLB) (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) :
    LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN' (lbIso_pull H h) b.symm)

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}

include h in

theorem iso_cubeLB_pull {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T) (H : LBIso L' (L.pull φ))
    {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : a'.left ≫ φ = U.left ≫ a.left) (hb : b'.left ≫ φ = U.left ≫ b.left) :
    LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) := by
  obtain ⟨w, hw⟩ := H
  refine LBIso.chartPull (chartPullId _) (chartPullOut L _ _ U.left _ fun I => ?_)
    (iso_linComb ((isGen_iff w).1 hw) _ _)
  refine psum_push h _ _ U (fun i => ?_) I.down
  fin_cases i
  exacts [Over.OverMorphism.ext ha, Over.OverMorphism.ext hb]

include h in

theorem prim_up (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w v : G ⟶ G} {w' v' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hv : v'.left ≫ φ = φ ≫ v.left) (A₁ : w * v = 𝟙 G)
    (A₂ : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ v] L))
    (A₃ : LBIso L (cubeLB G ![𝟙 G, w] L)) :
    w' * v' = 𝟙 G' ∧ LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ v'] L') ∧
      LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  let V : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have e₁ : (fst G' G').left ≫ φ = V.left ≫ (fst G G).left :=
    congrArg (fun q => q.left) (show pushPt h.1.w (fst G' G') = V ≫ fst G G from (lift_fst _ _).symm)
  have e₂ : (snd G' G').left ≫ φ = V.left ≫ (snd G G).left :=
    congrArg (fun q => q.left) (show pushPt h.1.w (snd G' G') = V ≫ snd G G from (lift_snd _ _).symm)
  refine ⟨Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w])), ?_, ?_⟩
  · rw [← h.2 G' w' v' (U ≫ w) (U ≫ v) hw.symm hv.symm, ← MonObj.comp_mul, A₁]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact iso_up (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
      (DVR.linComb_isLB _ hL' _ _)
      (iso_cubeLB_pull h V H (by rw [Over.comp_left, Over.comp_left, Category.assoc, hw, reassoc_of% e₁]) e₂)
      (iso_cubeLB_pull h V H e₁ (by rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% e₂])) A₂
  · have i : LBIso (cubeLB G' ![𝟙 G', w'] L') ((cubeLB G ![𝟙 G, w] L).pull φ) :=
      iso_cubeLB_pull h U H ((Category.id_comp _).trans (Category.comp_id _).symm) hw
    have a : (cubeLB G ![𝟙 G, w] L).IsLB := DVR.linComb_isLB _ hL _ _
    have a' : (cubeLB G' ![𝟙 G', w'] L').IsLB := DVR.linComb_isLB _ hL' _ _
    exact iso_up hL a hL' a' H i A₃

end Group

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem prim_of_isPEL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {a : J → 𝓞 E}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o} {t : TObj g k J b s} {τ : SAB H S} {w w' : J} (hw : a w = H.w0)
    (hw' : a w' = H.bar H.w0) (h : IsPEL D a bas ρ t τ) : t.Prim w w' := by
  obtain ⟨e, he, hL, hact, -⟩ := h
  letI := t.ab.comm
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h₁ : IsGrpPullback t.A τ.G (𝟙 _) e.inv.left := isGrpPullback_of_iso e.symm
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hL₁ : LBIso t.L (τ.PP.L.pull e.inv.left) :=
    LBIso.chartPull (chartPullSec t.L _ _ ih) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull τ.PP.L _ _ rfl) hL.symm
  have hj : ∀ j, (t.act j).left ≫ e.inv.left = e.inv.left ≫ (τ.act.act (a j)).left := fun j => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, hact, e.inv_hom_id_assoc]
  refine prim_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) (hj w') ?_ ?_ ?_
  · rw [hw, hw', ← τ.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, τ.act.one]
  · rw [hw, hw']; exact τ.adj _
  · rw [hw]; exact τ.prim

theorem prim_of_tMap {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S} {w w' : J} (T : TMap t' t f)
    (prim : t.Prim w w') : t'.Prim w w' := by
  obtain ⟨ψ, h', hL', -, hact'⟩ := T
  letI := t.ab.comm
  letI := t'.ab.comm
  exact prim_up h' t.isLB t'.isLB hL' (hact' w) (hact' w') prim.1 prim.2.1 prim.2.2

theorem locallyOfFiniteType_of_isQProjOver (h : IsQProjOver s) : LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str o N
  infer_instance

theorem tMap_constPt (L₁ : Out.Laws) (L₂ : Out.Laws2)
    (L₃ : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {K : Type} [Field K] {s : Sp (DualNumber K) ⟶ Sp o} (t : TObj g k J b s) {w w' : J} (prim : t.Prim w w')
    {Y : Scheme.{0}} {G : Over Y} [GrpObj G] {y : Sp (DualNumber K) ⟶ Y} {χ : t.A.left ⟶ G.left}
    (h : IsGrpPullback t.A G y χ) (hy : y = constPt y) : TMap t t (constPt (𝟙 _)) := by
  let q : Sp K ⟶ Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom
  let r : Sp (DualNumber K) ⟶ Sp K := spMap (algebraMap K (DualNumber K))
  have hqr : q ≫ r = 𝟙 _ := GlobalTheory.ConstTheta.fst_comp_const
  have hy' : y = r ≫ q ≫ y := hy
  obtain ⟨t₀, io, c₁, c₂, c₃, c₄⟩ := GlobalTheory.tObj_pull o g k J b _ _ s (q ≫ s) q t rfl
  have h₀ : IsGrpPullback t₀.A G (q ≫ y) (io ≫ χ) := c₁.comp h
  let ψ : t.A.left ⟶ t₀.A.left := h₀.1.lift χ (t.A.hom ≫ r) (by rw [h.1.w, Category.assoc, ← hy'])
  have i₁ : ψ ≫ io ≫ χ = χ := h₀.1.lift_fst _ _ _
  have i₂ : ψ ≫ t₀.A.hom = t.A.hom ≫ r := h₀.1.lift_snd _ _ _
  have k₀ : IsGrpPullback t.A t₀.A r ψ := h₀.cancel (h.congr hy' i₁.symm) i₂
  have k₁ : io ≫ ψ = 𝟙 _ := by
    apply h₀.1.hom_ext
    · rw [Category.assoc, i₁, Category.id_comp]
    · rw [Category.assoc, i₂, ← Category.assoc, c₁.1.w, Category.assoc, hqr, Category.id_comp, Category.comp_id]
  have T₁ := GlobalTheory.ConstTheta.tMap_of_const L₁ L₂ L₃ o g k J b w w' K _ _ t t₀ io ψ prim c₁ c₂ c₃ c₄ k₀ k₁
  have T₂ := tMap_comp T₁ ⟨io, c₁, c₂, c₃, c₄⟩
  unfold constPt
  rw [Category.comp_id]
  exact T₂

theorem formallyUnramified_and_locallyQuasiFinite : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)) (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TMap tT t f → TSieg bas bas' tT c → u ≫ pullback.snd _ _ = sT → SiegPB c Ag.univ (u ≫ pullback.fst _ _) → FormallyUnramified u ∧ LocallyQuasiFinite u := by
  intro L₁ L₂ L₃ E _ _ _ H D g J _ a w w' bas _ _ hw hw' _ k o _ b em ρ _ _ _ _ _ _ X s t τ hrep hpel p Ag _ _ _ bas' _
    O _ i z bb _ _ _ T sT f hT tT c u hm ⟨e, he, _⟩ hu ⟨φ, _, hφ, _⟩
  have h₁ := locallyOfFiniteType_of_isQProjOver hrep.qproj
  have h₂ : LocallyOfFiniteType (u ≫ pullback.snd _ _) := by
    rw [hu]; exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hT h₁
  refine GlobalTheory.TangentCriterion.unramified_quasiFinite_of_tangent _ _ u (locallyOfFiniteType_of_comp u (pullback.snd _ _)) fun K _ x hx => ?_
  have hc : ∀ {Y Z : Scheme.{0}} (y : Sp (DualNumber K) ⟶ Y) (v : Y ⟶ Z), constPt y ≫ v = constPt (y ≫ v) :=
    fun y v => by simp only [constPt, Category.assoc]
  obtain ⟨tx, Tx⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ x tT rfl
  obtain ⟨ψ, hψ, -⟩ := id Tx
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have g₁ := (hψ.comp (isGrpPullback_of_iso e.symm)).comp hφ
  have Tf := tMap_comp Tx hm
  have T₁ := tMap_constPt L₁ L₂ L₃ tx (prim_of_tMap Tf (prim_of_isPEL hw hw' hpel)) g₁ (by
    rw [Category.comp_id, ← hc, ← Category.assoc, hx, Category.assoc])
  have T₂ := tMap_comp T₁ Tf
  rw [hc, Category.id_comp, ← hc] at T₂
  have hs : x ≫ sT = constPt x ≫ sT := by rw [← hu, ← Category.assoc, hx, Category.assoc]
  refine hT.hom_ext (hrep.inj _ _ _ _ tx ?_ Tf T₂) hs
  rw [Category.assoc, Category.assoc, hT.w, ← Category.assoc, hs, Category.assoc]

end GlobalTheory.SiegUnram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Proof.TautologicalModel

section Taut

variable {X X' Y Z : Scheme.{0}}

theorem taut_le (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (J : PUnit → L.ι) (K : PUnit → PUnit → L.ι) :
    (L.pull (p ≫ F)).U J ⊓ ((L.pull F).pull p).U K ≤ (p ≫ F) ⁻¹ᵁ (L.U (J ⟨⟩) ⊓ L.U (K ⟨⟩ ⟨⟩)) := fun _ hy =>
  ⟨mem_pull.1 hy.1, mem_pull (L := L) (F := F).1 (mem_pull (L := L.pull F) (F := p).1 hy.2)⟩

def taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') : LB.Iso ((L.pull F).pull p) (L.pull (p ≫ F)) :=
  ⟨fun q => res (taut_le L F p q.1 q.2) (pullU (p ≫ F) _ (L.g (q.1 ⟨⟩) (q.2 ⟨⟩ ⟨⟩)))⟩

theorem gw_taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (f : Z ⟶ Y) (z : Z) (j : L.ι) (k : PUnit → PUnit → L.ι)
    (hj : (p ≫ F) (f z) ∈ L.U j) (hk : f z ∈ ((L.pull F).pull p).U k) :
    gw (taut L F p) f z j k = gm (f ≫ p ≫ F) z _ (L.g j (k ⟨⟩ ⟨⟩)) := by
  have hm : f z ∈ (L.pull (p ≫ F)).U (fun _ => j) ⊓ ((L.pull F).pull p).U k := ⟨mem_pull.2 hj, hk⟩
  exact (gm_res f z (taut_le L F p _ k) hm _).trans (gm_pull f (p ≫ F) z _ (taut_le L F p _ k hm) _)

theorem taut_isGen {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) (p : Y ⟶ X') : (taut L F p).IsGen := by
  refine (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_
  have h1 : (f ≫ p) z ∈ (L.pull F).U (k ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk
  have h1' : (f ≫ p) z ∈ (L.pull F).U (k' ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk'
  have h2 : (f ≫ p ≫ F) z ∈ L.U (k ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1
  have h2' : (f ≫ p ≫ F) z ∈ L.U (k' ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1'
  rw [gw_taut L F p f z j k hj hk, gw_taut L F p f z j' k' hj' hk', gm_pull_g (L.pull F) p f z k k' hk hk',
    gm_pull_g L F (f ≫ p) z _ _ h1 h1', Category.assoc,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j) (j := j') hj hj' h2,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j') (j := k ⟨⟩ ⟨⟩) hj' h2 h2']
  generalize gm (f ≫ p ≫ F) z _ (L.g j j') = A
  generalize gm (f ≫ p ≫ F) z _ (L.g j' (k ⟨⟩ ⟨⟩)) = B
  generalize gm (f ≫ p ≫ F) z _ (L.g (k ⟨⟩ ⟨⟩) (k' ⟨⟩ ⟨⟩)) = C
  rw [_root_.mul_comm B C, _root_.mul_assoc, inv_mul_cancel_left]

end Taut

section Rig

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem gm_rigPullOf (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) {Z : Scheme.{0}}
    (f : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (j : PUnit → PUnit → L.ι)
    (hj : f z ∈ LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) :
    gm f z (LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) ((rigPullOf F e he L r).s j) =
      gm (f ≫ e) z (LB.wchart L (fun _ : PUnit => eSec G) (fun _ => j ⟨⟩ ⟨⟩)) (r.s (fun _ => j ⟨⟩ ⟨⟩)) :=
  (gm_res f z (rigPull_le F e he L j) hj _).trans (gm_pull f e z _ (rigPull_le F e he L j hj) _)

theorem rigPullOf_isGen (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) :
    (rigPullOf F e he L r).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have hi' := rigPull_le F e he L i hy.1
  have hj' := rigPull_le F e he L j hy.2
  refine ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y i hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g (L.pull F) (eSec G') (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y j hy.2)))).trans ?_
  rw [gen_trans (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) hr (𝟙 _ ≫ e) y hi' hj', trF, Fintype.prod_unique,
    zpow_one, gm_pull_g L F (𝟙 _ ≫ eSec G') y (i ⟨⟩) (j ⟨⟩) (mem_pull (L := L.pull F) (F := eSec G').1 hy.1)
      (mem_pull (L := L.pull F) (F := eSec G').1 hy.2), Category.assoc, Category.assoc, he]

end Rig

end GlobalTheory.Proof.TautologicalModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaUniq

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_unit_of_local {R I : Type} [CommRing R] {v v' : I → R} (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ, ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a)) :
    ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 ((Ideal.eq_top_iff_one _).1 hv)
  have key : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ,
      algebraMap R (Localization.AtPrime q) (c.sum fun i a => a * v' i) = u ∧ ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a) := fun q _ => by
    obtain ⟨u, hu⟩ := h q
    refine ⟨u, ?_, hu⟩
    have e := congrArg (algebraMap R (Localization.AtPrime q)) hc
    simp only [Finsupp.sum, map_sum, map_mul, map_one] at e ⊢
    simp only [hu, mul_left_comm _ (u : Localization.AtPrime q)]
    rw [← Finset.mul_sum, e, _root_.mul_one]
  have hu : IsUnit (c.sum fun i a => a * v' i) := by
    by_contra hn
    obtain ⟨q, hq, hm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
    obtain ⟨u, e, -⟩ := key q
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).1 (e ▸ u.isUnit) hm
  refine ⟨hu.unit, fun a => Module.eq_of_localization_maximal (R := R) (fun q _ => Localization.AtPrime q)
    (fun q _ => Algebra.linearMap R (Localization.AtPrime q)) _ _ fun q _ => ?_⟩
  obtain ⟨u, e, e'⟩ := key q
  rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_mul, IsUnit.unit_spec, e, e']

theorem exists_ratio_base {X Y S₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = val u' r z J * gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL p e he hp (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine ⟨c, fun Z r z J hJ => ?_⟩
  rw [← hc Z r z J hJ, val_mul hJ, val_inv, mul_comm, inv_mul_cancel_right]

variable {S : Scheme.{0}} {T : Over S}

theorem exists_unit_of_isGenSec_local {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} [IsLocalRing Γ(T.left, ⊤)]
    {th th' : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (H' : IsGenSec A L k th') :
    ∃ u : Γ(T.left, ⊤)ˣ, SecM.ofSec A th = (u : Γ(T.left, ⊤)) • SecM.ofSec A th' := by
  obtain ⟨r, hr⟩ := H' th
  obtain ⟨r', hr'⟩ := H th'
  have e : SecM.ofSec A th = r • SecM.ofSec A th' := Subtype.ext (funext hr)
  have e' : SecM.ofSec A th' = r' • SecM.ofSec A th := Subtype.ext (funext hr')
  by_cases hu : IsUnit r
  · exact ⟨hu.unit, e⟩
  have h₁ : IsUnit (1 - r * r') :=
    (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left fun h => hu (isUnit_of_mul_isUnit_left h)
  have h₂ : SecM.ofSec A th = 0 := h₁.smul_eq_zero.1 (by rw [sub_smul, one_smul, mul_smul, ← e', ← e, sub_self])
  exact ⟨1, by rw [e', h₂, smul_zero, smul_zero]⟩

theorem exists_unit_over (hG : GlobalFnsSt) (P : PolAV S) [IsLocalRing Γ(T.left, ⊤)] {k : ℕ} (hk : Odd k) {I : Type}
    {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (H : IsThetaPtOver P k x v) (H' : IsThetaPtOver P k x v') :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ i, v' i = u * v i := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨th', s₁', α', τ', U', s₂', w', u', hth', hα', hτ', hs₁', hU', hs₂', hw', hv'⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec_local hth' hth
  obtain ⟨c, hc⟩ := exists_ratio_base hL (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst hG P.isAb T) hα' hα
  obtain ⟨d, hd⟩ := exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun a => ⟨a, rfl⟩) hτ hτ'
  have key : ∀ i, w' i = (ρ * c * d : Γ(T.left, ⊤)ˣ) * w i := fun i => fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart hL (χ z)
    replace hJ : Good P.L z J := hJ
    have a₀ : tval (U' i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J = tval (U i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      val_corr hJ (SymLiftOdd.symLift_unique hG P.isAb hL hk.pow _ _ (hU' i) (hU i)) _
    have a₁ : bval (b := 1) α' (lift (𝟙 T) (x i)).left z J =
        bval (b := 1) α (lift (𝟙 T) (x i)).left z J * gm (𝟙 T.left) z ⊤ c := by
      have := hc _ (lift (𝟙 T) (x i)).left z J hJ
      rw [lift_fst_left] at this
      exact this
    have a₂ := hd _ (𝟙 _) z J hJ
    have a₃ : sv P.A th' (lift (𝟙 T) (x i ^ k)).left z J =
        gs (𝟙 T.left) z ⊤ ρ * sv P.A th (lift (𝟙 T) (x i ^ k)).left z J := by
      have := ThetaAct.sv_smul (ρ : Γ(T.left, ⊤)) (SecM.ofSec P.A th) (lift (𝟙 T) (x i ^ k)).left z hJ
      rw [← hρ, lift_fst_left] at this
      exact this
    have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 T) hJ 1
    have b₂ := sv_mulPull hs₁ (𝟙 T) hJ (x i)
    have b₃ := sv_of_isValueAt (hw i) (𝟙 T) hJ
    have c₁ := sv_act (hU' i).pt_eq (hs₂' i) (𝟙 T) hJ 1
    have c₂ := sv_mulPull hs₁' (𝟙 T) hJ (x i)
    have c₃ := sv_of_isValueAt (hw' i) (𝟙 T) hJ
    rw [Category.id_comp, _root_.mul_one] at b₁ c₁
    rw [Category.id_comp] at b₃ c₃ a₂
    rw [b₃, b₂] at b₁
    rw [c₃, c₂, a₀, a₁, a₃] at c₁
    simp only [Over.id_left] at b₁ c₁
    rw [a₂] at b₁
    refine (Units.mul_left_inj (val τ' (𝟙 T.left) z J)).1 ?_
    rw [c₁, gs_mul _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, map_mul, map_mul]
    simp only [Units.val_mul] at b₁ ⊢
    linear_combination (-(gm (𝟙 T.left) z ⊤ ρ).val * (gm (𝟙 T.left) z ⊤ c).val) * b₁
  refine ⟨u' * (ρ * c * d) * u⁻¹, fun i => ?_⟩
  rw [hv', hv, key, Units.val_mul _ u⁻¹, _root_.mul_assoc _ _ (u * w i), Units.inv_mul_cancel_left, Units.val_mul u',
    _root_.mul_assoc (u' : Γ(T.left, ⊤))]

theorem isThetaPtOver_of_local (P : PolAV S) {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ S) {n : ℕ} {I : Type}
    {x : I → (Over.mk y ⟶ P.A)} {v : I → Γ((Over.mk y).left, ⊤)} (H : IsThetaPt P n x v) : IsThetaPtOver P n x v := by
  obtain ⟨V, hp, H'⟩ := H.2.2 (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  let h : Over.mk y ⟶ overRes (T := Over.mk y) ⊤ := Over.homMk (Sp R).topIso.inv (by
    show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ y = y
    rw [Scheme.toIso_inv_ι_assoc])
  have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
  have := isThetaPtOver_pull P H' h (overResι ⊤) hh
  convert this using 2 with a a
  · rw [← Category.assoc, hh, Category.id_comp]
  · have q := congrArg (fun q => q.left.appTop.hom (v a)) hh
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
      Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
    exact q.symm

theorem exists_unit_local (hG : GlobalFnsSt) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S)
    {v v' : Ix g (N' ^ 2) → R} (H : t.HasTh x v) (H' : t.HasTh x v') : ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  let e : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := e.symm.isLocalRing
  obtain ⟨u, hu⟩ := exists_unit_over hG t.pol H.1 (isThetaPtOver_of_local _ x H) (isThetaPtOver_of_local _ x H')
  refine ⟨Units.map e.toMonoidHom u, fun a => ?_⟩
  have q := (congrArg e (hu a)).trans (map_mul e _ _)
  exact (e.apply_symm_apply (v' a)).symm.trans (q.trans (congrArg (_ * ·) (e.apply_symm_apply (v a))))

end GlobalTheory.ThetaUniq

namespace GlobalTheory

theorem hasTh_unique_unit : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh x v' → Ideal.span (Set.range v) = ⊤ → ∃ u : Rˣ, ∀ a, v' a = u * v a :=
  fun h₁ h₂ o _ g N' J b S s t R _ x v v' H H' hv => ThetaUniq.exists_unit_of_local hv fun q _ =>
    ThetaUniq.exists_unit_local h₁.globalFns t _
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v H)
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v' H')

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionConstantFamilyDualNumbersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSection_constantFamily_dualNumbers : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  first | exact @GlobalTheory.KS.torsion_section_const | exact GlobalTheory.KS.torsion_section_const | (intros; apply GlobalTheory.KS.torsion_section_const <;> assumption)
end

