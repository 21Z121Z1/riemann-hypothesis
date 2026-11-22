import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierMonomialMemRadicalExtendedMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.PIsogExt

theorem comp_pow_pt {S : Scheme.{0}} {T T' A : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp_of_isGrpPullback {Y₀ Y : Scheme.{0}} {i : Y₀ ⟶ Y} {A₀ : Over Y₀} {A : Over Y}
    [GrpObj A₀] [GrpObj A] {φ : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A i φ) (k : ℕ) (hk : 0 < k) :
    (𝟙 A₀ ^ k).left ≫ φ = φ ≫ (𝟙 A ^ k).left := by
  let φ₀ : Over.mk (A₀.hom ≫ i) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (φ₀ ^ (n + 1)).left = (𝟙 A₀ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, pow_one]; rfl
    | succ n ih =>
      rw [pow_succ φ₀, pow_succ (𝟙 A₀)]
      exact h.2 A₀ _ _ _ _ ih rfl
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add, ← key n]
  have : φ₀ ^ (n + 1) = φ₀ ≫ 𝟙 A ^ (n + 1) := by rw [comp_pow_pt, Category.comp_id]
  rw [this]; rfl

theorem isSquare_square_compatible_homs {Y₀ Y : Scheme.{0}} {A₀ A₀' : Over Y₀} {A A' : Over Y}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A₀'] [IsCommMonObj A₀'] [GrpObj A] [IsCommMonObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A₀.left ⟶ A.left} {φ' : A₀'.left ⟶ A'.left}
    {φ₂ : (G2 A₀).left ⟶ (G2 A).left} {φ₂' : (G2 A₀').left ⟶ (G2 A').left}
    (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') {ψ₀ : A₀ ⟶ A₀'} {ψ : A ⟶ A'}
    (e : φ ≫ ψ.left = ψ₀.left ≫ φ') : φ₂ ≫ sq2 ψ = sq2 ψ₀ ≫ φ₂' := by
  have f1 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (fst B' B').left = (fst B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have f2 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (snd B' B').left = (snd B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  have g1 : sq2 ψ₀ ≫ (fst A₀' A₀').left = (fst A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have g2 : sq2 ψ₀ ≫ (snd A₀' A₀').left = (snd A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  apply pullback.hom_ext
  · change _ ≫ (fst A' A').left = _ ≫ (fst A' A').left
    rw [Category.assoc, Category.assoc, f1, h'.1, ← Category.assoc, h.1, Category.assoc, e, reassoc_of% g1]
  · change _ ≫ (snd A' A').left = _ ≫ (snd A' A').left
    rw [Category.assoc, Category.assoc, f2, h'.2, ← Category.assoc, h.2, Category.assoc, e, reassoc_of% g2]

open GlobalTheory.CechPic in

theorem lbIso_extend {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {Y₀ Y : Scheme.{0}} [IsLocallyNoetherian Y] (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    [IsDominant i] {σ₀ : Y₀ ⟶ Sp R} {σ : Y ⟶ Sp R} (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀)
    (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ) (c : ℕ) (h₀ : LBIso (Hecke.lbPow o₀.P c) (o₀'.P.pull (sq2 ψ₀))) :
    LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ)) := by
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI := o.ab.smooth
  haveI := o.ab.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom o.A o.A
  haveI := GlobalTheory.geometricallyConnected_tensorObj_hom o.A o.A
  have hpb : IsPullback m.φ₂ (G2 o₀.A).hom (G2 o.A).hom i := GlobalTheory.SiegDesc.isPullback_of_isSquare m.cart.1 m.sq
  have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have hM : (o'.P.pull (sq2 ψ)).IsLB := pull_isLB o'.isLB _
  have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
    fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
  let s : Y ⟶ (G2 o.A).left := (η[o.A] ≫ lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left
  have hs : s ≫ (G2 o.A).hom = 𝟙 Y := Over.w _
  have hss : s ≫ sq2 ψ = (η[o'.A] ≫ lift (1 : o'.A ⟶ o'.A) (𝟙 o'.A)).left := by
    rw [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [Hom.one_def, IsMonHom.one_hom]
  have r0 : ∀ (A : Over Y) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (hP : P.IsLB),
      (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
      pull (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0 := by
    intro A _ _ P hP ht
    rw [Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _), (cls_eq_zero_iff _).2 ht, map_zero]
  have key := eq_zero_of_pull_densePart_of_pull_section (G2 o.A).hom i m.φ₂ (G2 o₀.A).hom i.denseRange hpb s hs
    (cls _ hM - cls _ hL) ?_ ?_
  · exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 key).symm
  · have hsq := PIsogExt.isSquare_square_compatible_homs m.sq m'.sq e
    have e1 := (cls_eq_iff o₀'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have e2 := (cls_eq_iff o₀.isLB (pull_isLB o.isLB _)).2 m.pol
    have e3 : cls (Hecke.lbPow o₀.P c) (LB.isLB_linComb o₀.isLB _ _) = cls _ (pull_isLB o₀'.isLB (sq2 ψ₀)) :=
      (cls_eq_iff _ _).2 h₀
    rw [map_sub, sub_eq_zero, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hsq, pull_comp,
      ← cls_pull o'.isLB _ (pull_isLB o'.isLB _), ← e1, ← cls_pull o₀'.isLB _ (pull_isLB o₀'.isLB _), ← e3]
    refine (hcL (X := (G2 o₀.A).left) o₀.P o₀.isLB _).trans ?_
    rw [e2, cls_pull o.isLB]
  · rw [map_sub, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hss, r0 _ _ _ o'.rig₁, r0 _ _ _ o.rig₁,
      smul_zero, sub_zero]

theorem exists_isPIsog_extend : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ),
    3 ≤ N → N.Coprime p → ∀ (j c : ℕ), (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) →
    ∀ (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R), IsOpenImmersion i → IsDominant i →
    IsLocallyNoetherian Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) →
    (∀ y : Y, IsDomain (Y.presheaf.stalk y)) →
    ∀ (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A),
    IsPIsog c o₀ o₀' ψ₀ → ∃ ψ : o.A ⟶ o'.A, IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := by
  intro p _ D R _ b N _ _ j c _ Y₀ Y i σ₀ σ _ _ _ hic hdom o o' o₀ o₀' m m' ψ₀ hψ₀
  have hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := fun y => ⟨hdom y, hic y⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI : IsReduced Y := by
    haveI := hdom
    exact isReduced_of_isReduced_stalk Y
  have hcpos : 0 < c := hψ₀.pos
  obtain ⟨hk, hmon₀, hlin₀, heta₀, ⟨hP₀⟩, ψ₀', hmon₀', h₁, h₂⟩ := hψ₀
  haveI := hmon₀
  haveI := hmon₀'
  have hA := GlobalTheory.isSemiAbelian_of_isAbelianScheme o.A o.ab
  have hA' := GlobalTheory.isSemiAbelian_of_isAbelianScheme o'.A o'.ab
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.dense_openImmersion i
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o.A hA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o'.A hA'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o.A o'.A hA hA' o₀.A o₀'.A m.φ m'.φ
    m.cart m'.cart ψ₀ hmon₀
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o'.A o.A hA' hA o₀'.A o₀.A m'.φ m.φ
    m'.cart m.cart ψ₀' hmon₀'
  haveI hψm : IsMonHom ψ := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m.cart m'.cart ψ₀ ψ hψ
  haveI hψm' : IsMonHom ψ' := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m'.cart m.cart ψ₀' ψ' hψ'
  have e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := hψ.symm
  have e' : m'.φ ≫ ψ'.left = ψ₀'.left ≫ m.φ := hψ'.symm
  refine ⟨ψ, ⟨hk, hψm, fun c' => ?_, fun x => ?_, ⟨lbIso_extend hY i o o' o₀ o₀' m m' ψ₀ ψ e c hP₀⟩, ψ', hψm', ?_, ?_⟩, e⟩
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m.act c', Category.assoc, e, ← Category.assoc,
      ← Over.comp_left, hlin₀ c', Over.comp_left, Category.assoc, m'.act c', ← Category.assoc, ← e, Category.assoc]
  · refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant o'.A.hom (by rw [Over.w, Over.w]) i ?_)
    have h1 := m'.eta x
    have h2 := m.eta x
    rw [heta₀ x, Over.comp_left, Category.assoc] at h1
    rw [← h1, ← e, Over.comp_left, ← Category.assoc, h2, Category.assoc]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e, Category.assoc, e', ← Category.assoc, ← Over.comp_left, h₁,
      PIsogExt.pow_comp_of_isGrpPullback m.cart c hcpos]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m'.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e', Category.assoc, e, ← Category.assoc, ← Over.comp_left, h₂,
      PIsogExt.pow_comp_of_isGrpPullback m'.cart c hcpos]

end GlobalTheory.UPel.HT.ES.PIsogExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsOverFieldIrreducibleJoin
section
open CategoryTheory AlgebraicGeometry GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPath

theorem exists_path_auto : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (M : ι → (Spec (CommRingCat.of L)).Modules) (r : ι → ℕ), (∀ a, VB.IsVB (M a) (r a)) → ∀ φ : ∀ a, M a ≅ M a, ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (h₁ : t₁ ≫ c = 𝟙 _) (h₂ : t₂ ≫ c = 𝟙 _) (Φ : ∀ a, (Scheme.Modules.pullback c).obj (M a) ≅ (Scheme.Modules.pullback c).obj (M a)), IrreducibleSpace T ∧ (∀ a, (Scheme.Modules.pullback t₁).map (Φ a).hom = 𝟙 _) ∧ ∀ a, (Scheme.Modules.pullback t₂).map (Φ a).hom ≫ (Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a) = ((Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a)) ≫ (φ a).hom := by
  intro L _ ι _ M r hM φ
  have hframe : ∀ a, ∃ e : Fin (r a) → Γ(M a, ⊤), VB.IsFrame e := fun a => by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨U, e, hx, he⟩ := hM a x
    obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
    exact ⟨e, he⟩
  choose e he using hframe
  let K := Scheme.ΓSpecIso (CommRingCat.of L)
  let b : ∀ a, Module.Basis (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤) Γ(M a, ⊤) :=
    fun a => (he a).basis le_top
  have hb : ∀ a i, b a i = e a i := fun a i => by
    rw [VB.IsFrame.basis_apply, Twist.resM_self]
  let A' : ∀ a, Matrix (Fin (r a)) (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤) := fun a =>
    LinearMap.toMatrix (b a) (b a) (QCoh.appLinear (φ a).hom ⊤)
  let A : ∀ a, Matrix (Fin (r a)) (Fin (r a)) L := fun a => K.hom.hom.mapMatrix (A' a)
  have hA : ∀ a, IsUnit (A a).det := fun a => by
    have hu : IsUnit (LinearMap.det (QCoh.appLinear (φ a).hom ⊤)) :=
      LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (QCoh.appLinear (φ a).hom ⊤)
        (ConcreteCategory.bijective_of_isIso ((φ a).hom.app ⊤)))
    have : (A a).det = K.hom.hom (A' a).det := (RingHom.map_det _ _).symm
    rw [this, LinearMap.det_toMatrix]
    exact hu.map _
  have hAe : ∀ a i, (φ a).hom.app ⊤ (e a i) = ∑ j, K.inv (A a j i) • e a j := fun a i => by
    have hK : ∀ j, K.inv (A a j i) = A' a j i := fun j => by
      change K.inv (K.hom (A' a j i)) = _
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    simp only [hK, A', LinearMap.toMatrix_apply, ← hb]
    exact ((b a).sum_repr _).symm
  obtain ⟨T, c, t₁, t₂, h₁, h₂, B, hT, hB, hB₁, hB₂⟩ := GlobalTheory.T.frame_matrix_units_irreducible L ι r A hA
  have hq : ∀ a, (M a).IsQuasicoherent := fun a => (hM a).isQuasicoherent
  have hc : ∀ a, VB.IsFrame
      (fun i => QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i)) :=
    fun a => (he a).pullback c
  have hm : ∀ a, VB.IsFrame (fun j => ∑ i, B a i j •
      QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i)) :=
    fun a => FlagZ.Univ.isFrame_sum_smul_of_isUnit (hc a) (B a) (hB a)
  refine ⟨T, c, t₁, t₂, h₁, h₂, fun a => (hc a).iso (hm a), hT, fun a => ?_, fun a => ?_⟩
  · have H := GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₁ h₁ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom
      (B a) (fun i => (hc a).iso_hom_app (hm a) i) (𝟙 _) (fun i => by
        simp only [hB₁, Matrix.one_apply]
        simp [apply_ite])
    refine (cancel_mono ((Scheme.Modules.pullbackComp t₁ c).hom.app (M a) ≫
      (Scheme.Modules.pullbackCongr h₁).hom.app (M a) ≫
      (Scheme.Modules.pullbackId _).hom.app (M a))).1 ?_
    exact H.trans ((Category.comp_id _).trans (Category.id_comp _).symm)
  · exact GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₂ h₂ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom
      (B a) (fun i => (hc a).iso_hom_app (hm a) i) (φ a).hom (fun i => by
        simp only [hB₂]
        exact hAe a i)

end GlobalTheory.FlagPath

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

namespace GlobalTheory.FlagCell

theorem steps_iso_of_spans_top : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl₁ fl₂ : Vert.Flag F m) (v : Fin m → Γ(F, ⊤)), Spans fl₁ ⊤ v → Spans fl₂ ⊤ v → ∀ i, ∃ e : fl₁.F i ≅ fl₂.F i, e.hom ≫ fl₂.ι i = fl₁.ι i := by
  intro X F m fl₁ fl₂ v h₁ h₂ i
  obtain ⟨s₁, hs₁, e₁⟩ := h₁ i
  obtain ⟨s₂, hs₂, e₂⟩ := h₂ i
  exact GlobalTheory.VB.exists_iso_of_frames_app_eq (fl₁.ι i) (fl₂.ι i) (i : ℕ)
    fun _ => ⟨⊤, s₁, s₂, trivial, hs₁, hs₂, fun j => (e₁ j).trans (e₂ j).symm⟩

end GlobalTheory.FlagCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatNormalFibersOpenExtension
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem rule_eq_on_extend_chart : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (N : ℕ) (M : Scheme.{0}) (sM : M ⟶ Sp (Localization.Away (N : ℤ)))
    (U : Obj F 𝔠 M) (V : M.Opens), Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W),
    (∀ (W' : M.Opens) (hW' : IsAffineOpen W'), W' ≤ W ⊓ V → ∀ (Y' : Obj F 𝔠 (Sp Γ(M, W')))
      (φ' : Y'.A.left ⟶ U.A.left), Y'.IsPullBy U hW'.fromSpec φ' → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : Γ(M, W') →+* B) (Y'' : Obj F 𝔠 (Sp B)) (φ'' : Y''.A.left ⟶ Y'.A.left),
    Y''.IsPullBy Y' (spMap σ) φ'' → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y''.DetGen), s.val B Y'' h δ = t.val B Y'' h δ)) →
    ∀ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φ →
    ∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W))) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ := by
  intro F _ _ 𝔠 R₀ _ k s t N M sM U V hflat hnorm hcodim W hW hagree Y φ hY YC ψ hYC h δ
  set d := s.val _ YC h δ - t.val _ YC h δ with hd
  suffices hd0 : TensorProduct.comm ℤ R₀ Γ(M, W) d = 0 by
    have : d = 0 := by simpa using congrArg (TensorProduct.comm ℤ R₀ Γ(M, W)).symm hd0
    exact sub_eq_zero.mp this
  refine rTensor_eq_zero_of_restrict_affine_inf N M sM V hflat hnorm hcodim W hW R₀ _ ?_
  intro W' hW' hle
  let ρ : Γ(M, W) →+* Γ(M, W') := (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom
  let τ' : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W') :=
    Algebra.TensorProduct.map (AlgHom.id R₀ R₀) ρ.toIntAlgHom
  have hswap : ∀ x : R₀ ⊗[ℤ] Γ(M, W), LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap
      (TensorProduct.comm ℤ R₀ Γ(M, W) x) = TensorProduct.comm ℤ R₀ Γ(M, W') (τ' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [τ']
    | add x y hx hy => simp only [map_add, hx, hy]
  change LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap _ = 0
  rw [hswap]
  suffices hτ : τ' d = 0 by rw [hτ, map_zero]

  let incR : Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W) :=
    (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom
  let incR' : Γ(M, W') →+* R₀ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.includeRight : Γ(M, W') →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W')).toRingHom
  obtain ⟨Y', φ', hY'⟩ := Obj.exists_isPullBy U hW'.fromSpec
  obtain ⟨YC', ψ', hYC'⟩ := Obj.exists_isPullBy YC (spMap (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')))
  have hcomm : (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')).comp incR = incR'.comp ρ := by
    ext x; simp [τ', incR, incR']
  have hbase : spMap (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')) ≫ spMap incR ≫ hW.fromSpec =
      spMap incR' ≫ hW'.fromSpec := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomm, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
    congr 1
    exact hW.map_fromSpec hW' (homOfLE (hle.trans inf_le_left)).op
  have hall := hYC'.comp (hYC.comp hY)
  rw [hbase] at hall
  obtain ⟨ψ'', hψ'', -⟩ := hall.cancel hY'
  obtain ⟨δ', hδ', -⟩ := hYC'.existsUnique_detGen _ δ
  have h' : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W')) := map_natCast τ' 6 ▸ h.map τ'
  have heq := hagree W' hW' hle Y' φ' hY' (R₀ ⊗[ℤ] Γ(M, W')) incR' YC' ψ'' hψ'' h' δ'
  have hs := s.baseChange _ _ τ' YC h YC' h' ψ' δ δ' hYC' hδ'
  have ht := t.baseChange _ _ τ' YC h YC' h' ψ' δ δ' hYC' hδ'
  rw [hd, map_sub, ← hs, ← ht, heq, sub_self]

end GlobalTheory.RealMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrimeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrder_wedge_eq_of_etaleTower_heightOnePrime : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = P0.formOrd (dForm cK (fun i => (x i : K))) := by
  first | exact @GlobalTheory.FieldPair.formOrd_append_of_ord_eq | exact GlobalTheory.FieldPair.formOrd_append_of_ord_eq | (intros; apply GlobalTheory.FieldPair.formOrd_append_of_ord_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem coord_of_formalEnd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  intro R _ _ _ _ D a a' h h' hE A G _ _ _ U b ⟨hb, _, hq, ht⟩ α u ⟨hu, hu1⟩ e Z x z J hJ
  obtain ⟨t, ht, hi⟩ := ht e
  have := hb e
  have := (U.gt e).q_hom
  obtain ⟨v, hv, vv⟩ := GlobalTheory.gtCoord_end_ratio_descends R (maximalIdeal R) D.toPre e G (U.gt e) (b e) a h' t
    (hb e) ht hi (hq e) α
  have hA : IsAbelianScheme (thickObj R (maximalIdeal R) e D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have key := gen_unique D.toPre.P.isLB (thickObj R (maximalIdeal R) e D.toPre.P.A).hom
    (η[thickObj R (maximalIdeal R) e D.toPre.P.A]).left (Over.w _) (GlobalTheory.globalFns_holds _ _ hA).2 hv
    (DVR.pullGen_isGen _ _ _ _ hu (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)))
    (fun y J hJ => by
      have k := vv _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
          thickObj R (maximalIdeal R) e D.toPre.P.A) = η[thickObj R (maximalIdeal R) e D.toPre.P.A] := by
        simp [Hom.one_def]
      rw [o] at k
      exact k.symm.trans ((hu1 _ (thick R (maximalIdeal R) e) y J hJ).symm.trans
        ((congrArg (fun p => val u p y J)
          (UnitValue.eSec_pullback_fst (thick R (maximalIdeal R) e) D.toPre.P.A).symm).trans
          (val_pull hJ _ _ _).symm)))
  refine (vv Z x z J hJ).trans (congrArg (_ * ·) ((key Z _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)))
  exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSumTwistCubeIdentity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem formEq_twist_cube : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := by
  intro R _ _ D₂ D T Y₀ q y p₂ β _ hp b χ₂ χ U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k = ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) ^ (Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β = (q ≫ y) * (toUnit T ≫ D₂.c χ₂ ≫ β) := by
    rw [MonObj.mul_comp, hp, Category.assoc]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (D.Oφ (q ≫ y) χ k) ^ (-Oinvε k) = h ((q ≫ y) * (toUnit T ≫ D.c χ)).left *
      (h (toUnit T ≫ D.c χ).left)⁻¹ * (h (q ≫ y).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((q ≫ y) * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (q ≫ y).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ) = _
    simp only [zpow_neg, zpow_one, inv_inv]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, prod_cub, hC, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    h0, h3, hp, _root_.one_mul, Category.assoc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierMonomialMemRadicalExtendedMaximalIdealStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierMonomial_mem_radical_extended_maximalIdeal : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 3 ≤ N₁ → Φ.Exact N₁ → ∀ (y : Φ.Y) (nu : Fin s → Φ.X y), nu ≠ 0 → mono W (Φ.t y) (Φ.δ y) nu ∈ ((maximalIdeal A).map (Φ.ev y)).radical := by
  first | exact @GlobalTheory.Poinc.RadQ.mono_mem_radical | exact GlobalTheory.Poinc.RadQ.mono_mem_radical | (intros; apply GlobalTheory.Poinc.RadQ.mono_mem_radical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSumsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.ClassSums N₁ → Φ.Four N₁ := by
  first | exact @GlobalTheory.Poinc.SFour.four_of_classSums | exact GlobalTheory.Poinc.SFour.four_of_classSums | (intros; apply GlobalTheory.Poinc.SFour.four_of_classSums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSumsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 1 ≤ s → 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ := by
  first | exact @GlobalTheory.Poinc.SepLam.lam_of_exact | exact GlobalTheory.Poinc.SepLam.lam_of_exact | (intros; apply GlobalTheory.Poinc.SepLam.lam_of_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentInvariantMorphismFlatExistsUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisDescent_invariant_morphism_flat_existsUnique : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃! h₀ : Y ⟶ W, β ≫ h₀ = h := by
  first | exact @GlobalTheory.GalDescent.descend | exact GlobalTheory.GalDescent.descend | (intros; apply GlobalTheory.GalDescent.descend <;> assumption)
end

