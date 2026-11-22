import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroup
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActOfGenerators
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.UnderMap

theorem sec_ext_of_pow_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (u v : 𝟙_ (Over S) ⟶ G) (h : u ^ n = v ^ n)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      toUnit (Over.mk x) ≫ u = toUnit (Over.mk x) ≫ v) : u = v := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA S G n hn
  have h₂ : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have e : ∀ w : 𝟙_ (Over S) ⟶ G, w ≫ Out.mulA G n = w ^ n := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA G n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, h]) (Set.eq_univ_of_forall fun p => ?_)
  let k := AlgebraicClosure (S.residueField p)
  let x : Sp k ⟶ S := spMap (algebraMap (S.residueField p) k) ≫ S.fromSpecResidueField p
  have hx : x ≫ u.left = x ≫ v.left := by
    have := congrArg (fun z => z.left) (hg k x)
    simp only [Over.comp_left, ObjPull.toUnit_left'] at this
    exact this
  refine range_subset_range_equalizer_ι (T := S) x hx ⟨(default : PrimeSpectrum k), ?_⟩
  show S.fromSpecResidueField p _ = p
  exact Scheme.fromSpecResidueField_apply p _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem map_zero_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c) :
    F 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem map_nsmul_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (n : ℕ) (a : A) : F (n • a) = F a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, map_zero_of_add h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

def eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) : AddSubgroup A :=
  AddMonoidHom.eqLocus (AddMonoidHom.mk' (fun a => Additive.ofMul (F a)) fun a c => congrArg Additive.ofMul (h a c))
    (AddMonoidHom.mk' (fun a => Additive.ofMul (F' a)) fun a c => congrArg Additive.ofMul (h' a c))

theorem mem_eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) (a : A) : a ∈ eqSub h h' ↔ F a = F' a := Iff.rfl

theorem eta_eq_pow {B : Type} [CommRing B] {bB : Base l B} {S : Scheme.{0}} {sB : S ⟶ Sp B} (ob : Obj D l bB sB)
    (hd : l.M ∣ l.A) (a : D.La) (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ob.eta a = ob.etaA a ^ (l.A / l.M) := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hq : 0 < l.A / l.M := Nat.div_pos (Nat.le_of_dvd l.A_pos hd) hM
  have hA : l.M * (l.A / l.M) = l.A := Nat.mul_div_cancel' hd
  have hp := ob.proper
  have hn : IsUnit (l.M : Γ(S, ⊤)) := by
    simpa using (bB.unit l.M hM).map (sB.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
  refine sec_ext_of_pow_eq ob.t.G l.M hn _ _ ?_ fun k _ _ x => ?_
  · rw [← pow_mul, mul_comm, hA, ← map_nsmul_of_add ob.etaA_add, ob.etaA_ker, ← map_nsmul_of_add ob.eta_add]
    apply ob.eta_ker
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine Submodule.smul_mem_smul ?_ trivial
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    rw [l.prod] at hle
    exact hle (Ideal.mem_span_singleton_self _)
  · obtain ⟨β, hβ⟩ : ∃ β : B →+* k, x ≫ sB = spMap β := ⟨(Spec.preimage (x ≫ sB)).hom, (Spec.map_preimage _).symm⟩
    obtain ⟨-, I, -, h₁, h₂⟩ := ob.geom k x β hβ
    rw [h₂ a ha, MonObj.comp_pow, h₁ a, ← I.tower l.M (l.A / l.M) hM hq a, hA]

section Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {bB : Base l B} {bB' : Base l B'} {S S' : Scheme.{0}}
  {sB : S ⟶ Sp B} {sB' : S' ⟶ Sp B'} {f : S' ⟶ S}

theorem eq_secPull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (u' : 𝟙_ (Over S') ⟶ G') (u : 𝟙_ (Over S) ⟶ G) :
    u' = ObjPull.secPull h u ↔ u'.left ≫ φ = f ≫ u.left := by
  refine ⟨fun e => e ▸ ObjPull.secPull_left h u, fun e => ?_⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · rw [e, ObjPull.secPull_left]
  · rw [Over.w, Over.w]

theorem levels_of_basis (ob : Obj D l bB sB) (ob' : Obj D l bB' sB') (hd : l.M ∣ l.A) {n : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] D.La) {φ : ob'.t.G.left ⟶ ob.t.G.left} (h : IsGrpPullback ob'.t.G ob.t.G f φ)
    (hb : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ φ = f ≫ (ob.etaA (bas (Pi.single i 1))).left) :
    (∀ a, (ob'.eta a).left ≫ φ = f ≫ (ob.eta a).left) ∧ ∀ a, (ob'.etaA a).left ≫ φ = f ≫ (ob.etaA a).left := by
  have hA : ∀ a, ob'.etaA a = ObjPull.secPull h (ob.etaA a) := by
    intro a
    have add : ∀ a c, ObjPull.secPull h (ob.etaA (a + c)) =
        ObjPull.secPull h (ob.etaA a) * ObjPull.secPull h (ob.etaA c) := fun a c => by rw [ob.etaA_add, map_mul]
    refine (mem_eqSub (F' := fun a => ObjPull.secPull h (ob.etaA a)) ob'.etaA_add add a).1 ?_
    obtain ⟨c, rfl⟩ := bas.surjective a
    have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j; simp [Pi.single_apply]
    rw [hc, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    refine zsmul_mem ?_ _
    exact (eq_secPull h _ _).2 (hb i)
  refine ⟨fun a => (eq_secPull h _ _).1 ?_, fun a => (eq_secPull h _ _).1 (hA a)⟩
  have ha : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at ha
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
  rw [ob.eta_add, ob'.eta_add, ob.eta_ker _ h₁, ob'.eta_ker _ h₁, _root_.one_mul, _root_.one_mul,
    eta_eq_pow ob hd _ h₂, eta_eq_pow ob' hd _ h₂, map_pow, hA]

theorem act_of_generators {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (α : OAct O G) (α' : OAct O G') {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {J : Type} (a : J → O)
    (ha : Subring.closure (Set.range a) = ⊤)
    (hj : ∀ j, (α'.act (a j)).left ≫ φ = φ ≫ (α.act (a j)).left) (c : O) :
    (α'.act c).left ≫ φ = φ ≫ (α.act c).left := by
  have add' : ∀ a c, pushHom h G' (α'.act (a + c)) = pushHom h G' (α'.act a) * pushHom h G' (α'.act c) :=
    fun a c => by rw [α'.add, map_mul]
  have add : ∀ a c, pushHom h G' (𝟙 _) ≫ α.act (a + c) =
      (pushHom h G' (𝟙 _) ≫ α.act a) * (pushHom h G' (𝟙 _) ≫ α.act c) :=
    fun a c => by rw [α.add, MonObj.comp_mul]
  have key : ∀ c, c ∈ eqSub (F := fun c => pushHom h G' (α'.act c))
      (F' := fun c => pushHom h G' (𝟙 _) ≫ α.act c) add' add ↔ (α'.act c).left ≫ φ = φ ≫ (α.act c).left := fun c => by
    rw [mem_eqSub]
    have e : (pushHom h G' (𝟙 _) ≫ α.act c).left = φ ≫ (α.act c).left :=
      congrArg (· ≫ (α.act c).left) (Category.id_comp φ)
    exact ⟨fun H => (congrArg (fun z => z.left) H).trans e, fun H => Over.OverMorphism.ext (H.trans e.symm)⟩
  have hc : c ∈ Subring.closure (Set.range a) := by rw [ha]; trivial
  rw [← key]
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact (key _).2 (hj j)
  | zero => exact zero_mem _
  | one => rw [key, α.one, α'.one]; simp
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    rw [key] at hx hy ⊢
    rw [α.mul, α'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

end Pull

theorem objMap_iff_tMap : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (B o : Type) [CommRing B] [CommRing o] (bB : Base l B) (b : TBase o l.A) (S S' : Scheme.{0}) (sB : S ⟶ Sp B) (sB' : S' ⟶ Sp B) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (ob : Obj D l bB sB) (ob' : Obj D l bB sB') (t : TObj g l.A J b s) (t' : TObj g l.A J b s') (f : S' ⟶ S), l.M ∣ l.A → Subring.closure (Set.range a) = ⊤ → ObjUnder ob a bas t → ObjUnder ob' a bas t' → (Nonempty (ObjMap ob' ob f) ↔ TMap t' t f) := by
  intro hL _ E _ _ _ H D g J a bas l B o _ _ bB b S S' sB sB' s s' ob ob' t t' f hd ha
    ⟨e, he, heL, hea, hep⟩ ⟨e', he', heL', hea', hep'⟩
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have ih' : e'.inv.left ≫ e'.hom.left = 𝟙 _ := by rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]
  have hi' : e'.hom.left ≫ e'.inv.left = 𝟙 _ := by rw [← Over.comp_left, e'.hom_inv_id, Over.id_left]
  have m₁ : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have m₂ : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have a₁ : ∀ j, (ob.t.act.act (a j)).left ≫ e.hom.left = e.hom.left ≫ (t.act j).left := fun j =>
    congrArg (fun z => z.left) (hea j)
  have a₂ : ∀ j, (ob'.t.act.act (a j)).left ≫ e'.hom.left = e'.hom.left ≫ (t'.act j).left := fun j =>
    congrArg (fun z => z.left) (hea' j)
  have p₁ : ∀ i, (ob.etaA (bas (Pi.single i 1))).left ≫ e.hom.left = (t.pt i).left := hep
  have p₂ : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ e'.hom.left = (t'.pt i).left := hep'
  constructor
  · rintro ⟨m⟩
    have mL : LBIso ob'.t.PP.L (ob.t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    refine ⟨e'.inv.left ≫ m.cm.F ≫ e.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
    · exact (IsGrpPullback.comp (isGrpPullback_of_iso e'.symm)
        (IsGrpPullback.comp m.cart (isGrpPullback_of_iso e))).congr (by simp) rfl
    · have k₁ : LBIso (ob'.t.PP.L.pull e'.inv.left) (t'.L.pull (𝟙 _)) := PELPull.lbIso_pull heL' e'.inv.left ih'.symm
      have k₂ : LBIso t'.L (ob'.t.PP.L.pull e'.inv.left) :=
        k₁.symm.chartPull (chartPullUnpull t'.L _ rfl) (chartPullId _)
      have k₃ : LBIso ob'.t.PP.L (t.L.pull (m.cm.F ≫ e.hom.left)) :=
        mL.trans ob'.t.PP.isLB (pull_isLB ob.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull heL m.cm.F rfl)
      exact k₂.trans t'.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull k₃ e'.inv.left rfl)
    · have := m.etaA (bas (Pi.single i 1))
      rw [← p₂, ← p₁, Category.assoc, reassoc_of% hi']
      exact (reassoc_of% this) _
    · have h₂ : (t'.act j).left ≫ e'.inv.left = e'.inv.left ≫ (ob'.t.act.act (a j)).left := by
        rw [← Category.id_comp (t'.act j).left, ← ih', Category.assoc, Category.assoc, ← reassoc_of% a₂ j, hi',
          Category.comp_id]
      have h₃ := m.act (a j)
      rw [reassoc_of% h₂, reassoc_of% h₃, a₁, Category.assoc, Category.assoc]
  · rintro ⟨ψ, hψ, hψL, hpt, hact⟩
    have hc : IsGrpPullback ob'.t.G ob.t.G f (e'.hom.left ≫ ψ ≫ e.inv.left) :=
      (IsGrpPullback.comp (isGrpPullback_of_iso e')
        (IsGrpPullback.comp hψ (isGrpPullback_of_iso e.symm))).congr (by simp) rfl
    have kL : LBIso ob'.t.PP.L (ob.t.PP.L.pull (e'.hom.left ≫ ψ ≫ e.inv.left)) := by
      have k₁ : LBIso ob'.t.PP.L (t.L.pull (e'.hom.left ≫ ψ)) :=
        heL'.trans ob'.t.PP.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL e'.hom.left rfl)
      refine k₁.trans ob'.t.PP.isLB (pull_isLB t.isLB _) (pull_isLB ob.t.PP.isLB _)
        (PELPull.lbIso_pull heL _ ?_).symm
      rw [Category.assoc, Category.assoc, ih, Category.comp_id]
    obtain ⟨m, hm⟩ := GlobalTheory.exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' ob.t ob'.t f _ ob.proper hc kL
      (act_of_generators ob.t.act ob'.t.act hc a ha fun j => by
        have h₂ : (t.act j).left ≫ e.inv.left = e.inv.left ≫ (ob.t.act.act (a j)).left := by
          rw [← Category.id_comp (t.act j).left, ← ih, Category.assoc, Category.assoc, ← reassoc_of% a₁ j, hi,
            Category.comp_id]
        rw [reassoc_of% a₂ j, reassoc_of% hact j, h₂, Category.assoc, Category.assoc])
    obtain ⟨q₁, q₂⟩ := levels_of_basis ob ob' hd bas hc fun i => by
      have := hpt i
      rw [reassoc_of% p₂ i]
      refine ((reassoc_of% this) _).trans ?_
      rw [← p₁]
      exact congrArg (f ≫ ·) (by rw [Category.assoc, hi, Category.comp_id])
    rw [← hm] at q₁ q₂
    exact ⟨⟨m, q₁, q₂⟩⟩

end GlobalTheory.UnderMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertField

theorem differentiableAt_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) :
    DifferentiableAt ℂ (fun z => (M z).det) z₀ := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem differentiableAt_adjugate_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀)
    (i j : Fin g) : DifferentiableAt ℂ (fun z => (M z).adjugate i j) z₀ := by
  simp only [Matrix.adjugate_apply]
  refine differentiableAt_det (fun z => (M z).updateRow j (Pi.single i 1)) z₀ fun k l => ?_
  by_cases hk : k = j <;> simp [Matrix.updateRow_apply, hk, h k l]

theorem differentiableAt_of_mulVec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (b w : E → Fin g → ℂ) (z₀ : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) (hb : ∀ i, DifferentiableAt ℂ (fun z => b z i) z₀)
    (hdet : (M z₀).det ≠ 0) (hw : ∀ᶠ z in nhds z₀, (M z).mulVec (w z) = b z) :
    DifferentiableAt ℂ w z₀ := by
  have hd : DifferentiableAt ℂ (fun z => (M z).det) z₀ := differentiableAt_det M z₀ h
  have hne : ∀ᶠ z in nhds z₀, (M z).det ≠ 0 := hd.continuousAt.eventually_ne hdet
  have heq : w =ᶠ[nhds z₀] fun z => ((M z).det)⁻¹ • ((M z).adjugate.mulVec (b z)) := by
    filter_upwards [hne, hw] with z hz hzw
    rw [← hzw, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hz, one_smul]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  rw [differentiableAt_pi]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hadj := differentiableAt_adjugate_apply M z₀ h i
  have hi := hd.inv hdet
  fun_prop

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  have hpre : (x ≫ φ) ⁻¹ᵁ U = x ⁻¹ᵁ φ ⁻¹ᵁ U := by simp
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · rw [dif_pos (by rwa [hpre]), dif_pos h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dif_neg (by rwa [hpre]), dif_neg h]

theorem isOpen_dom_and_differentiableOn_fn {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left}
    (u : HolUnif A₀ L₀ g) {X : Scheme.{0}} (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    IsOpen (dom u m W) ∧ DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have hcomp : ∀ z, ((u.ex z).left ≫ m) ⁻¹ᵁ W = (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W := fun z => by simp
  have hdom : dom u m W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W} := by
    ext z
    simp only [dom, Set.mem_ofPred_eq, hcomp]
  have hfn : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
    funext z
    exact valAt'_comp _ _ _ _
  rw [hdom, hfn]
  exact u.8 (m ⁻¹ᵁ W) ((m.app W).hom f)

private theorem clm_apply_eq_sum_single_mul {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ a, L (Pi.single a 1) * v a := by
  have hv : v = ∑ a, v a • (Pi.single a 1 : Fin g → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_differentiableOn_vertical : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by
  intro P₀ u Hm χ hU R _ x₀ X p m hsm hpb n B G s hB hGd hs hhol
  have key : ∀ z ∈ B, ∃ v : Fin P₀.g → ℂ, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) v :=
    fun z hz => (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hsm hpb (G z) (s z) (hs z hz).1 (hs z hz).2).exists
  choose! w hw using key
  refine ⟨w, fun z₁ hz₁ => ?_, hw⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨W, t, hW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hU R x₀ X p m hsm hpb (G z₁)
  have hD : IsOpen (dom u m W) := (isOpen_dom_and_differentiableOn_fn u m W 0).1
  have hV : IsOpen {z ∈ B | G z ∈ dom u m W} := hB.inter (hD.preimage hGd.continuous)
  have hz₁V : z₁ ∈ {z ∈ B | G z ∈ dom u m W} := ⟨hz₁, hW⟩
  have hT : Matrix.transpose (Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1)) =
      Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1) := by
    ext a b
    rfl
  refine differentiableAt_of_mulVec (fun z => Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z) (Pi.single a 1))
    (fun z b => s z W (t b)) w z₁ (fun b a => ?_) (fun b => ?_) ?_ ?_
  · have h1 := ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex P₀.g (dom u m W) (fn u m W (t b)) hD).2
      (isOpen_dom_and_differentiableOn_fn u m W (t b)).2).2 (Pi.single a 1)
    exact (h1.differentiableAt (hD.mem_nhds hW)).comp z₁ (hGd z₁)
  · exact (hhol W (t b)).differentiableAt (hV.mem_nhds hz₁V)
  · rw [← Matrix.det_transpose, hT]
    exact hdet
  · filter_upwards [hV.mem_nhds hz₁V] with z hz
    ext b
    exact ((hw z hz.1 W (t b) hz.2).trans (clm_apply_eq_sum_single_mul _ _)).symm

end GlobalTheory.KS.VertField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_coords_det_fderiv_ne_zero_of_smooth : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  first | exact @GlobalTheory.KS.exists_fibre_coords | exact GlobalTheory.KS.exists_fibre_coords | (intros; apply GlobalTheory.KS.exists_fibre_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_scheme_latticeTorsionHom_primitiveRoot : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  first | exact @GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | exact GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | (intros; apply GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.exists_isPEL_of_tmap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S) (f : S' ⟶ S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g J a bas k o _ b ρ S S' s s' t t' τ f hs ht hP

  exact GlobalTheory.PELPull.isPEL_pull E H D g k J a bas o b ρ S S' s s' f t t' τ hs ht hP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull j), (∃ i, σ.f i ≠ 0) → ∃ (c : K) (s : LB.Sec M), c ≠ 0 ∧ (∀ i, (j.app (M.U i)).hom (s.f i) = cst fK (j ⁻¹ᵁ M.U i) c * rs XK (le_pull M j le_rfl) (σ.f (fun _ => i))) ∧ ∃ x ∈ Out.nonzeroLocus s, f x = IsLocalRing.closedPoint O := by
  first | exact @GlobalTheory.exists_smul_sec_nonzero_on_special_fibre | exact GlobalTheory.exists_smul_sec_nonzero_on_special_fibre | (intros; apply GlobalTheory.exists_smul_sec_nonzero_on_special_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  first | exact @GlobalTheory.TorsionTheta.exists_theta | exact GlobalTheory.TorsionTheta.exists_theta | (intros; apply GlobalTheory.TorsionTheta.exists_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s') (f : S' ⟶ S) (R : Type) [CommRing R] (x : Sp R ⟶ S') (v : Ix g (N' ^ 2) → R), TMap t' t f → (t'.HasTh x v ↔ t.HasTh (x ≫ f) v) := by
  first | exact @GlobalTheory.hasTh_iff_of_tmap | exact GlobalTheory.hasTh_iff_of_tmap | (intros; apply GlobalTheory.hasTh_iff_of_tmap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.torsion_local_presentation_smooth_group : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O), ptMap ε ≫ y = 1 → ∀ (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) ∧ RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) ∧ (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) ∧ (∀ i, ρ (x i) = MvPowerSeries.X i) ∧ ∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0 := by
  first | exact @GlobalTheory.TorsionPres.local_presentation | exact GlobalTheory.TorsionPres.local_presentation | (intros; apply GlobalTheory.TorsionPres.local_presentation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.valuationRing_henselian_and_smooth_points_lift : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K], HenselianLocalRing O ∧ IsAlgClosed (IsLocalRing.ResidueField O) ∧ ∀ (X : Scheme.{0}) (f : X ⟶ Sp O), Smooth f → ∀ x : Sp (IsLocalRing.ResidueField O) ⟶ X, x ≫ f = spMap (IsLocalRing.residue O) → ∃ y : Sp O ⟶ X, y ≫ f = 𝟙 _ ∧ spMap (IsLocalRing.residue O) ≫ y = x := by
  first | exact @GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed | exact GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed | (intros; apply GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsLocalOnBaseOfOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilIs_local_on_base_of_openCover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  first | exact @GlobalTheory.weilIs_of_openCover | exact GlobalTheory.weilIs_of_openCover | (intros; apply GlobalTheory.weilIs_of_openCover <;> assumption)
end

