import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem push_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

omit [GrpObj A] [GrpObj A'] in

theorem lift_sq (sq : IsSquare φ φ₂) {T : Over S} {T' : Over S'} (χ : T.left ⟶ T'.left) (x' y' : T' ⟶ A')
    {Z : Over S} (ψ : T.left ⟶ Z.left) (x y : Z ⟶ A) (hx : χ ≫ x'.left ≫ φ = ψ ≫ x.left)
    (hy : χ ≫ y'.left ≫ φ = ψ ≫ y.left) : χ ≫ (lift x' y').left ≫ φ₂ = ψ ≫ (lift x y).left := by
  refine pullback.hom_ext (f := A.hom) (g := A.hom) ?_ ?_
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (fst A A).left = (ψ ≫ (lift x y).left) ≫ (fst A A).left
    rw [Category.assoc, Category.assoc, sq.1, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_fst, hx,
      Category.assoc, ← Over.comp_left, lift_fst]
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (snd A A).left = (ψ ≫ (lift x y).left) ≫ (snd A A).left
    rw [Category.assoc, Category.assoc, sq.2, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_snd, hy,
      Category.assoc, ← Over.comp_left, lift_snd]

omit [GrpObj A] [GrpObj A'] in

theorem diag_iso (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (H : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  obtain ⟨u, hu⟩ := H
  have e : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (𝟙 A')
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  exact LBIso.chartPull (chartPullId _) (chartPullOut P _ _ φ _ fun _ => e)
    (iso_linComb ((isGen_iff u).1 hu) (fun _ : PUnit => (lift (𝟙 A') (𝟙 A')).left) (fun _ => 1))

theorem nondeg_pull (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ((hn _ (pushHom h T x) ?_).trans (map_one _).symm)
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

def secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S') ⟶ A' :=
  Over.homMk (h.1.lift (f ≫ x.left) (𝟙 S') (by
    rw [Category.assoc, Over.w x]; exact (Category.comp_id _).trans (Category.id_comp _).symm)) (h.1.lift_snd _ _ _)

theorem secPull_left (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : (secPull h x).left ≫ φ = f ≫ x.left :=
  h.1.lift_fst _ _ _

theorem push_secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) (T : Over S') :
    pushHom h T (toUnit T ≫ secPull h x) = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secPull h x).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, secPull_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem push_secPull' (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) :
    pushHom h _ (secPull h x) = toUnit _ ≫ x := by
  have e := push_secPull h x (𝟙_ (Over S'))
  rwa [toUnit_unit, Category.id_comp] at e

end GlobalTheory.SiegelPull

namespace GlobalTheory

open SiegelPull

theorem siegPre_pullback : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (c : SiegPre h M ζ s), f ≫ s = s' → (∃ c' : SiegPre h M ζ s', SiegPB c' c f) ∧ ∀ c' : SiegPre h M ζ s', SiegPB c' c f → c.Principal → c'.Principal := by
  intro h M o _ ζ S S' s s' f c hs
  refine ⟨?_, ?_⟩
  · obtain ⟨p⟩ := siegPairPB_nonempty c f
    refine ⟨{
      A := p.A
      ab := p.ab
      P := p.P
      isLB := p.isLB
      rig₁ := p.rig₁
      rig₂ := p.rig₂
      symm := p.symm
      lev := fun a => secPull p.pb (c.lev a)
      lev_add := fun a b => push_injective p.pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', c.lev_add, MonObj.comp_mul])
      lev_tors := fun a => push_injective p.pb _ (by
        rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
      geom := fun k _ _ x β z hx hz => ?_ }, p.φ, p.φ₂, p.pb, p.sq, p.iso, fun a => secPull_left p.pb _⟩
    obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective p.pb (Over.mk x)).eq_iff, push_secPull, map_one]
      rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom p.pb (Over.mk x) g) (by
        have := congrArg (pushHom p.pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective p.pb _ ((push_secPull p.pb _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S S' c.A p.A f p.φ _ _ (pull_isLB c.isLB _) (pull_isLB p.isLB _) p.pb
        (diag_iso p.sq p.iso) (Over.mk x) M _ _ _ _ _
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b)
  · rintro c' ⟨φ, φ₂, pb, sq, iso, -⟩ ⟨h₁, h₂⟩
    exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
      (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelPullComp

theorem iso_pull {X Y : Scheme.{0}} {L M : LB X} (d : Y ⟶ X) (h : LBIso L M) : LBIso (L.pull d) (M.pull d) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨LB.linCombIso w (fun _ : PUnit => d) (fun _ => 1), DVR.linCombIso_isGen w hw _ _⟩

private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (x : Γ(X, U)ˣ) : gm f y V (res h x) = gm f y U x := by
  unfold gm
  rw [dif_pos hy, dif_pos (h hy)]
  simp only [MonoidHom.comp_apply]
  rw [pullU_res₂]
  ext
  simp [res]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem lbIso_of_chart_le_of_gm_transition_eq {Y : Scheme.{0}} {A' B : LB Y} (hB : LBIso B B) (idx : A'.ι → B.ι)
    (le : ∀ i, A'.U i ≤ B.U (idx i))
    (hg : ∀ (y : Y) i j, y ∈ A'.U i → y ∈ A'.U j →
      gm (𝟙 Y) y (A'.U i ⊓ A'.U j) (A'.g i j) = gm (𝟙 Y) y (B.U (idx i) ⊓ B.U (idx j)) (B.g (idx i) (idx j))) :
    LBIso A' B := by
  obtain ⟨w, hw⟩ := hB
  have cp : ChartPull (B.div A') (B.div B) (𝟙 Y) :=
    { idx := fun p => (p.1, idx p.2)
      le := fun p y hy => ⟨hy.1, le p.2 hy.2⟩
      g := by
        rintro y ⟨p1, p2⟩ ⟨q1, q2⟩ hp hq
        have hp' : y ∈ B.U p1 ⊓ A'.U p2 := hp
        have hq' : y ∈ B.U q1 ⊓ A'.U q2 := hq
        change gm (𝟙 Y) y ((B.U p1 ⊓ A'.U p2) ⊓ (B.U q1 ⊓ A'.U q2)) (res _ (B.g p1 q1) * (res _ (A'.g p2 q2))⁻¹) =
          gm (𝟙 Y) y ((B.U p1 ⊓ B.U (idx p2)) ⊓ (B.U q1 ⊓ B.U (idx q2)))
            (res _ (B.g p1 q1) * (res _ (B.g (idx p2) (idx q2)))⁻¹)
        rw [map_mul, map_mul, map_inv, map_inv, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y,
          gm_res_eq_gm (𝟙 Y) y, hg y p2 q2 hp'.2 hq'.2]
        all_goals first
          | exact ⟨hp', hq'⟩
          | exact ⟨⟨hp'.1, le _ hp'.2⟩, ⟨hq'.1, le _ hq'.2⟩⟩ }
  obtain ⟨t, ht⟩ := gen_chartPull cp w hw
  exact ⟨t, ht⟩

theorem iso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (d : Z ⟶ Y) :
    LBIso ((L.pull a).pull d) (L.pull (d ≫ a)) := by
  have base : LBIso (L.pull (d ≫ a)) (L.pull (d ≫ a)) :=
    exists_iso_linComb hL (fun _ : PUnit => d ≫ a) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ K : ((L.pull a).pull d).ι, ((L.pull a).pull d).U K ≤ (L.pull (d ≫ a)).U (fun _ => K ⟨⟩ ⟨⟩) :=
    fun K y hy => by
      have h1 : d y ∈ (L.pull a).U (K ⟨⟩) := mem_pull.1 hy
      have h2 : a (d y) ∈ L.U (K ⟨⟩ ⟨⟩) := mem_pull.1 h1
      exact mem_pull.2 h2
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun K _ => K ⟨⟩ ⟨⟩) le ?_
  intro y K K' hK hK'
  rw [gm_pull_g (L.pull a) d (𝟙 Z) y K K' hK hK', gm_pull_g L (d ≫ a) (𝟙 Z) y _ _ (le K hK) (le K' hK')]
  simp only [Category.id_comp]
  rw [gm_pull_g L a d y (K ⟨⟩) (K' ⟨⟩) (mem_pull.1 hK) (mem_pull.1 hK')]

theorem iso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) := by
  have base : LBIso (L.pull (𝟙 X)) (L.pull (𝟙 X)) :=
    exists_iso_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ i : L.ι, L.U i ≤ (L.pull (𝟙 X)).U (fun _ => i) := fun i y hy => mem_pull.2 hy
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun i _ => i) le ?_
  intro y i j hi hj
  rw [gm_pull_g L (𝟙 X) (𝟙 X) y _ _ (le i hi) (le j hj), Category.id_comp]

variable {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem pb_id (c : SiegPre h k ζ s) : SiegPB c c (𝟙 _) := by
  unfold SiegPB
  have : IsMonHom (Iso.refl c.A).hom := by
    show IsMonHom (𝟙 c.A)
    infer_instance
  refine ⟨𝟙 _, 𝟙 _, ?_, ?_, iso_pull_id c.isLB, fun a => by simp⟩
  · exact (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl
  · unfold Geo.Tor.IsSquare
    simp

theorem pb_comp {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (m' : SiegPB c'' c' f') : SiegPB c'' c (f' ≫ f) := by
  unfold SiegPB at m m' ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hg', ⟨ht1, ht2⟩, hl', hlev'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hg'.comp hg, ?_, ?_, fun a => ?_⟩
  · unfold Geo.Tor.IsSquare
    constructor
    · rw [Category.assoc, hs1, ← Category.assoc, ht1, Category.assoc]
    · rw [Category.assoc, hs2, ← Category.assoc, ht2, Category.assoc]
  · exact LBIso.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB c.isLB _) hl'
      (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull ψ₂ hl) (iso_pull_pull c.isLB φ₂ ψ₂))
  · rw [← Category.assoc, hlev' a, Category.assoc, hlev a, ← Category.assoc]

private theorem hom_ext_tensor_left_of_fst_snd_eq {T : Scheme.{0}} {A : Over T} {X : Scheme.{0}} {a b : X ⟶ (A ⊗ A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b := by
  have hw : b ≫ (A ⊗ A).hom = a ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← Category.assoc, h₁]
  have key : (Over.homMk a rfl : Over.mk (a ≫ (A ⊗ A).hom) ⟶ A ⊗ A) = Over.homMk b hw := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₁
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₂
  exact congrArg CommaMorphism.left key

theorem pb_cancel {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (n : SiegPB c'' c (f' ≫ f)) : SiegPB c'' c' f' := by
  unfold SiegPB at m n ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hn, ⟨ht1, ht2⟩, hln, hlevn⟩ := n
  have hw : ψ ≫ c.A.hom = (c''.A.hom ≫ f') ≫ f := by rw [hn.1.w, Category.assoc]
  obtain ⟨χ, hχ1, hχ2⟩ : ∃ χ : c''.A.left ⟶ c'.A.left, χ ≫ φ = ψ ∧ χ ≫ c'.A.hom = c''.A.hom ≫ f' :=
    ⟨hg.1.lift ψ (c''.A.hom ≫ f') hw, hg.1.lift_fst _ _ _, hg.1.lift_snd _ _ _⟩
  have hgc : IsGrpPullback c''.A c'.A f' χ := IsGrpPullback.cancel hg (hn.congr rfl hχ1.symm) hχ2
  have q1 : ((fst c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (fst c''.A c''.A)]
    rfl
  have q2 : ((snd c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (snd c''.A c''.A)]
    rfl
  obtain ⟨χ₂, hq1, hq2⟩ : ∃ χ₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left,
      χ₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ χ ∧
      χ₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ χ := by
    refine ⟨(lift (Over.homMk _ q1 : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A) (Over.homMk _ q2)).left, ?_, ?_⟩
    · rw [← Over.comp_left, lift_fst]
      rfl
    · rw [← Over.comp_left, lift_snd]
      rfl
  have e : χ₂ ≫ φ₂ = ψ₂ := by
    apply hom_ext_tensor_left_of_fst_snd_eq
    · rw [Category.assoc, hs1, ← Category.assoc, hq1, Category.assoc, hχ1, ht1]
    · rw [Category.assoc, hs2, ← Category.assoc, hq2, Category.assoc, hχ1, ht2]
  refine ⟨χ, χ₂, hgc, ⟨hq1, hq2⟩, ?_, fun a => ?_⟩
  · rw [← e] at hln
    exact LBIso.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB c'.isLB _) hln
      (LBIso.symm (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull χ₂ hl) (iso_pull_pull c.isLB φ₂ χ₂)))
  · apply hg.1.hom_ext
    · simp only [Category.assoc, hχ1, hlevn, hlev]
    · simp only [Category.assoc, hχ2]
      rw [reassoc_of% (Over.w (c''.lev a)), Over.w (c'.lev a)]
      simp

theorem id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  intro h k B B' B'' _ _ _ ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f'
  exact ⟨pb_id c, fun m => ⟨fun m' => pb_comp m m', fun n => pb_cancel m n⟩⟩

end GlobalTheory.SiegelPullComp
end
end

