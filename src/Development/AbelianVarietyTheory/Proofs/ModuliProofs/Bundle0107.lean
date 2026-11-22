import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

noncomputable section

namespace GlobalTheory.SquareGenerated

section
variable {X Y : Scheme.{0}} {H : LB X}

theorem unitAt_of_mem (s : LB.Sec H) (φ : Y ⟶ X) (y : Y) (hy : φ y ∈ Out.nonzeroLocus s) :
    UnitAt H (K := Fin 1) (fun _ => φ) (fun _ => 1) y := by
  have v : ∀ (j : Fin 1 → H.ι) (z : Y), z ∈ LB.wchart H (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z (LB.wchart H (fun _ : Fin 1 => φ) j)
        ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))) = gs (𝟙 Y ≫ φ) z (H.U (j 0)) (s.f (j 0)) := fun j z hz =>
    (gs_res _ z _ hz _).trans (gs_pull _ φ z _ (LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz) _)
  let s' : LB.Sec (LB.LinComb H (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            (congrArg Units.val (gm_linComb H _ _ (𝟙 Y) z j j' hz.1 hz.2)))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        have hm : (𝟙 Y ≫ φ) z ∈ H.U (j 0) ⊓ H.U (j' 0) :=
          ⟨LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz.1, LB.wchart_le H (fun _ : Fin 1 => φ) j' 0 hz.2⟩
        refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res _ z _ hm _))))
        rw [gs_unit _ z _ hm, Fin.prod_univ_one, zpow_one] }
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => k) ?_⟩
  have hm : y ∈ LB.wchart H (fun _ : Fin 1 => φ) (fun _ => k) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ hk
  show y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op).hom
          ((φ.app _).hom (s.f k)))
  have e := Y.basicOpen_res ((φ.app _).hom (s.f k))
    (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op
  refine e ▸ ⟨hm, ?_⟩
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f k)) y).1 hk

theorem exists_sec_pw (hH : H.IsLB) (t : ℤ) (y : X)
    (h : UnitAt H (K := Fin 1) (fun _ => 𝟙 X) (fun _ => t) y) :
    ∃ u : LB.Sec (pw H t), y ∈ Out.nonzeroLocus u := by
  obtain ⟨s, hs⟩ := h
  have le : ∀ i : H.ι, H.U i ≤ LB.wchart H (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i z hz => Set.mem_iInter.2 fun _ => hz
  let u : LB.Sec (pw H t) :=
    { f := fun i => (X.presheaf.map (homOfLE (le i)).op).hom (s.f fun _ => i)
      compat := fun i j => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le i) hz.1 _)).trans
          (Eq.trans ?_ ((gs_mul (𝟙 X) z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit (𝟙 X) z _ hz _)
              ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le j) hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (le i hz.1) (le j hz.2)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
        exact (Fin.prod_univ_one _).trans (map_zpow _ _ _).symm }
  choose I hI using fun χ : X ⟶ X => exists_chart hH (χ y)
  have hm : y ∈ H.U (I (𝟙 X ≫ 𝟙 X)) := hI (𝟙 X ≫ 𝟙 X)
  refine ⟨u, TopologicalSpace.Opens.mem_iSup.2 ⟨I (𝟙 X ≫ 𝟙 X), (X.mem_basicOpen _ _ hm).2 ?_⟩⟩
  exact (congrArg IsUnit ((gs_eq (𝟙 X) y _ hm _).symm.trans (gs_res (𝟙 X) y (le _) hm _))).mpr (hs I hI)

end

theorem exists_sec_sq {O : Type} [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    {H : LB A.left} (hH : H.IsLB) (hT : Triv (Theta A H)) (s : LB.Sec H) (a : 𝟙_ (Over (Sp O)) ⟶ A)
    (y : A.left) (h₁ : ((toUnit A ≫ a) * 𝟙 A).left y ∈ Out.nonzeroLocus s)
    (h₂ : ((toUnit A ≫ a⁻¹) * 𝟙 A).left y ∈ Out.nonzeroLocus s) :
    ∃ u : LB.Sec (pw H 2), y ∈ Out.nonzeroLocus u := by
  obtain ⟨t, ht⟩ := hT
  let χ : Fin 4 → (Sp O ⟶ A.left) := ![(a * a⁻¹).left, a.left, (a⁻¹).left, (1 : 𝟙_ (Over (Sp O)) ⟶ A).left]
  choose i hi using fun k => exists_chart hH (χ k (IsLocalRing.closedPoint O))
  have e : ∀ k, (![((toUnit A ≫ a) * (toUnit A ≫ a⁻¹)).left, (toUnit A ≫ a).left,
      (toUnit A ≫ a⁻¹).left, (1 : A ⟶ A).left] k) = (toUnit A).left ≫ χ k := by
    intro k
    fin_cases k
    · show _ = (toUnit A ≫ (a * a⁻¹)).left
      rw [MonObj.comp_mul]; rfl
    · rfl
    · rfl
    · show _ = (toUnit A ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A)).left
      rw [MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := GlobalTheory.AbSquare.exists_gen_square hH t ht (toUnit A ≫ a) (toUnit A ≫ a⁻¹) (𝟙 A) i
    (fun k z => by
      rw [e k]
      have h : χ k ⁻¹ᵁ H.U (i k) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
      show (toUnit A).left z ∈ χ k ⁻¹ᵁ H.U (i k)
      rw [h]; trivial)
  have hu' : UnitAt H _ _ y := ⟨genSec u hu, fun J hJ => by
    rw [sval_genSec u hu _ y hJ]; exact Units.isUnit _⟩
  have e1 : (toUnit A ≫ a) * (toUnit A ≫ a⁻¹) * 𝟙 A = 𝟙 A := by
    rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
  refine exists_sec_pw hH 2 y (UnitAt.congr hH (formEq_of_add fun U _ hh => ?_)
    (((unitAt_of_mem s _ y h₁).mul (unitAt_of_mem s _ y h₂)).mul hu'))
  simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, e1, Sum.elim_inl, Sum.elim_inr]
  simp
  module

theorem exists_secs_sq_generate : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro O K _ _ _ _ _ _ _ A _ _ hA H hH hT s hs
  obtain ⟨-, hk, hlift⟩ := GlobalTheory.T.valuationRing_henselian_and_smooth_points_lift O K
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let t : Sp (IsLocalRing.ResidueField O) ⟶ Sp O := spMap (IsLocalRing.residue O)
  let T : Over (Sp O) := Over.mk t
  have : IsIntegral (T ⊗ A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.hom).flip
  let p : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint (IsLocalRing.ResidueField O)
  have htp : t p = IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have up : ∀ x : A.left, A.hom x = IsLocalRing.closedPoint O → ∃ z : (T ⊗ A).left, (snd T A).left z = x := by
    intro x hx
    have : x ∈ Set.range (pullback.snd t A.hom) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨p, htp.trans hx.symm⟩
    exact this
  let W : A.left.Opens := ⨆ u : LB.Sec (pw H 2), Out.nonzeroLocus u
  have hW : W = ⊤ := by
    by_contra hne
    have hZ : ((W : Set A.left)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (SetLike.coe_injective h)
    have hc : IsClosed (A.hom '' (W : Set A.left)ᶜ) := A.hom.isClosedMap _ W.isOpen.isClosed_compl
    obtain ⟨x₀, hx₀, hx₁⟩ : IsLocalRing.closedPoint O ∈ A.hom '' (W : Set A.left)ᶜ := by
      obtain ⟨q, hq⟩ := hZ.image A.hom
      exact (IsLocalRing.specializes_closedPoint q).mem_closed hc hq
    obtain ⟨z₀, hz₀⟩ := up x₀ hx₁
    have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left :=
      inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
    have : JacobsonSpace (T ⊗ A).left :=
      LocallyOfFiniteType.jacobsonSpace (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left
    obtain ⟨c, hcZ, hcc⟩ := nonempty_inter_closedPoints
      (Z := (((snd T A).left ⁻¹ᵁ W : (T ⊗ A).left.Opens) : Set (T ⊗ A).left)ᶜ)
      ⟨z₀, by
        show ¬ (snd T A).left z₀ ∈ W
        rw [hz₀]; exact hx₀⟩ ((snd T A).left ⁻¹ᵁ W).isOpen.isClosed_compl.isLocallyClosed
    let σ := pointOfClosedPoint (X := (T ⊗ A).left) (K := IsLocalRing.ResidueField O) (fst T A).left c hcc
    have hσ : σ ≫ (fst T A).left = 𝟙 _ := pointOfClosedPoint_comp _ c hcc
    have hσp : σ p = c := pointOfClosedPoint_apply _ c hcc p
    let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
      rw [← Over.w (fst T A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
    let x : T ⟶ A := σ' ≫ snd T A
    have hx : x.left p ∉ W := by
      show (snd T A).left (σ p) ∉ W
      rw [hσp]; exact hcZ
    obtain ⟨y₀, hy₀, hy₁⟩ := hs
    obtain ⟨z₁, hz₁⟩ := up y₀ hy₁
    obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t ((snd T A).left ⁻¹ᵁ Out.nonzeroLocus s)
      ⟨z₁, by
        show (snd T A).left z₁ ∈ Out.nonzeroLocus s
        rw [hz₁]; exact hy₀⟩ x x
    obtain ⟨b, hb, hba⟩ := hlift A.left A.hom inferInstance a.left (Over.w a)
    let b' : 𝟙_ (Over (Sp O)) ⟶ A := Over.homMk b hb
    have hb' : toUnit T ≫ b' = a := Over.OverMorphism.ext hba
    have key : ∀ (d : 𝟙_ (Over (Sp O)) ⟶ A), (Out.ptSecT A ((toUnit T ≫ d) * x)).left p ∈
        (snd T A).left ⁻¹ᵁ Out.nonzeroLocus s →
        ((toUnit A ≫ d) * 𝟙 A).left (x.left p) ∈ Out.nonzeroLocus s := by
      intro d hd
      have e : x ≫ ((toUnit A ≫ d) * 𝟙 A) = Out.ptSecT A ((toUnit T ≫ d) * x) ≫ snd T A := by
        simp [Out.ptSecT, MonObj.comp_mul]
      have e' : ((toUnit A ≫ d) * 𝟙 A).left (x.left p) =
          (snd T A).left ((Out.ptSecT A ((toUnit T ≫ d) * x)).left p) :=
        congrArg (fun q => q.left p) e
      rw [e']; exact hd
    obtain ⟨u, hu⟩ := exists_sec_sq A hH hT s b' (x.left p) (key b' (by rw [hb']; exact h₁ p))
      (key b'⁻¹ (by rw [GrpObj.comp_inv, hb']; exact h₂ p))
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨u, hu⟩)
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec (pw H 2) => (Out.nonzeroLocus u : Set A.left)) (fun u => (Out.nonzeroLocus u).isOpen)
    (fun y _ => by
      have : y ∈ W := by rw [hW]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i : LB.Sec (pw H 2))), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end GlobalTheory.SquareGenerated
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjTheta

theorem prod_ev {M Q : Type} [AddCommGroup M] [Group Q] {m : ℕ} (ev : M → Q) (add : ∀ a c, ev (a + c) = ev a * ev c)
    (bas : (Fin m → ℤ) ≃ₗ[ℤ] M) (c : Fin m → ℕ) :
    (List.ofFn fun i => ev (bas (Pi.single i 1)) ^ c i).prod = ev (bas fun i => (c i : ℤ)) := by
  let f : Multiplicative M →* Q := MonoidHom.mk' (fun x => ev x.toAdd) fun a b => add _ _
  have h : (fun i => ev (bas (Pi.single i 1)) ^ c i) =
      f ∘ fun i => Multiplicative.ofAdd (bas (Pi.single i 1)) ^ c i := by
    funext i
    exact (map_pow f (Multiplicative.ofAdd (bas (Pi.single i 1))) (c i)).symm
  rw [h, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn]
  show ev _ = _
  congr 1
  rw [toAdd_prod]
  simp only [toAdd_pow, toAdd_ofAdd, ← map_nsmul, ← map_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem ev_pow {M Q : Type} [AddCommGroup M] [Group Q] (ev : M → Q) (add : ∀ a c, ev (a + c) = ev a * ev c)
    (n : ℕ) (a : M) : ev a ^ n = ev (n • a) :=
  (map_pow (MonoidHom.mk' (fun x : Multiplicative M => ev x.toAdd) fun _ _ => add _ _) (Multiplicative.ofAdd a) n).symm

theorem existsUnique_label {M Q : Type} [AddCommGroup M] [Group Q] {m n : ℕ} (hn : 0 < n) (ev : M → Q)
    (add : ∀ a c, ev (a + c) = ev a * ev c) (ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b)
    (bas : (Fin m → ℤ) ≃ₗ[ℤ] M) {y : Q} (hy : ∃ a, ev a = y) :
    ∃! c : Fin m → ZMod n, (List.ofFn fun i => ev (bas (Pi.single i 1)) ^ (c i).val).prod = y := by
  have : NeZero n := ⟨hn.ne'⟩
  have key : ∀ u v : Fin m → ℤ, ev (bas u) = ev (bas v) ↔ ∀ i, (u i : ZMod n) = v i := by
    intro u v
    have e : ev (bas u) = ev (bas (u - v)) * ev (bas v) := by rw [← add, ← map_add, sub_add_cancel]
    rw [e, mul_eq_right, ker]
    constructor
    · rintro ⟨b, hb⟩ i
      obtain ⟨w, rfl⟩ := bas.surjective b
      rw [← map_nsmul] at hb
      have := congrFun (bas.injective hb) i
      simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at this
      rw [← sub_eq_zero, ← Int.cast_sub, this]
      simp
    · intro h
      have : ∀ i, ∃ w : ℤ, u i - v i = n * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by rw [Int.cast_sub, h, sub_self])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨u, rfl⟩ := bas.surjective a
  refine ⟨fun i => (u i : ZMod n), ?_, fun c hc => ?_⟩
  · beta_reduce
    rw [prod_ev ev add, key]
    intro i
    simp
  · beta_reduce at hc
    rw [prod_ev ev add, key] at hc
    funext i
    simpa using hc i

theorem root_ext {S : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {u v : Γ(S, ⊤)ˣ} (hu : u ^ n = 1) (hv : v ^ n = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      Units.map x.appTop.hom.toMonoidHom u = Units.map x.appTop.hom.toMonoidHom v) : u = v := by
  let w : Γ(S, ⊤) := (u * v⁻¹ : Γ(S, ⊤)ˣ)
  have hw : w ^ n = 1 := by
    have : (u * v⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hu, hv, inv_one, _root_.mul_one]
    exact congrArg Units.val this
  have unit : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    refine RingedSpace.isUnit_of_isUnit_germ S.toLocallyRingedSpace.toRingedSpace ⊤ _ fun p hp => ?_
    refine (S.mem_basicOpen _ p hp).1 ?_
    let K := AlgebraicClosure (S.residueField p)
    let x : Sp K ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) K)) ≫ S.fromSpecResidueField p
    have hx : x (default : PrimeSpectrum K) = p := Scheme.fromSpecResidueField_apply p _
    have h1 : x.appTop.hom w = 1 := by
      have : Units.map x.appTop.hom.toMonoidHom (u * v⁻¹) = 1 := by
        rw [map_mul, map_inv, h K x, mul_inv_cancel]
      exact congrArg Units.val this
    have h2 : IsUnit (x.appTop.hom (∑ i ∈ Finset.range n, w ^ i)) := by
      rw [map_sum]
      simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
      simpa using hn.map x.appTop.hom
    have h3 : x ⁻¹ᵁ S.basicOpen (∑ i ∈ Finset.range n, w ^ i) = ⊤ := by
      rw [Scheme.preimage_basicOpen_top]
      exact Scheme.basicOpen_of_isUnit _ h2
    rw [← hx]
    exact (h3.ge : _) (Set.mem_univ (default : PrimeSpectrum K))
  have h0 : w - 1 = 0 := by
    have := geom_sum_mul w n
    rw [hw, sub_self] at this
    exact (unit.mul_right_eq_zero).1 this
  exact mul_inv_eq_one.1 (Units.ext (sub_eq_zero.1 h0))

theorem exists_weilIs_root (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (P : Out.PolAV S) (t : LB.Gen (Theta P.A P.L))
    (ht : t.IsGen) (n : ℕ) {T : Over S} {x y : T ⟶ P.A} (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, Out.WeilIs P.A P.L n x y c ∧ c ^ n = 1 := by
  have := P.isAb.comm
  have loc : ∀ z : T ⟶ P.A, z ^ n = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp P.A P.L n (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨V, hV, H⟩ := (KerPow.locGen_theta_iff P.isLB P.ktriv
      (fun a c => (KerPow.locGen_iff _ _ _).1 (AbSquare.square_local P.isLB t ht T a c)) z n).2 hz p
    exact ⟨V, hV, KerPow.exists_theta z n V H⟩
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs hG P.isAb P.isLB (loc x hx) (loc y hy)
  have pw : ∀ m : ℕ, Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := fun m => by
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hc
    | succ m ih => rw [pow_succ x (m + 1), pow_succ c (m + 1)]; exact weilIs_mul_left hG S P n T _ _ _ _ _ ih hc
  have e := pw n
  rw [pow_succ x, hx, _root_.one_mul] at e
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB e hc
  rw [pow_succ, mul_eq_right] at this
  exact ⟨c, hc, this⟩

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  have e₁ := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  have e₂ := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e₁ e₂
  exact e₁.trans e₂.symm

theorem exists_tObj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (B o : Type) [CommRing B] [CommRing o] (bB : Base l B) (b : TBase o l.A) (ρ : o) (j : o →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (ob : Obj D l bB s), IsSympBasis D bas → j ρ = bB.ρ → j (b.ζ : o) = bB.ζ → ∃ t : TObj g l.A J b (s ≫ spMap j), ObjUnder ob a bas t ∧ IsPEL D a bas ρ t ob.t := by
  intro hL _ E _ _ _ H D g J a bas l B o _ _ bB b ρ j S s ob hbas hρ hζ
  have hG := hL.globalFns
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have h₁ := finrank_int_lattice D
    have h₂ := bas.finrank_eq
    rw [Module.finrank_fin_fun] at h₂
    omega
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ ob.t.G) := fun i => toUnit _ ≫ ob.etaA (bas (Pi.single i 1))
  have hpt : ∀ (T : Over S) (f : T ⟶ Out.baseOver S) (i), f ≫ pt i = toUnit T ≫ ob.etaA (bas (Pi.single i 1)) :=
    fun T f i => by rw [← Category.assoc, comp_toUnit]
  have tors : ∀ i, pt i ^ l.A = 1 := fun i => by
    rw [← MonObj.comp_pow, ev_pow ob.etaA ob.etaA_add, ob.etaA_ker, MonObj.comp_one]
  have hβ : ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x ≫ s = spMap (Spec.preimage (x ≫ s)).hom :=
    fun K _ x => (Spec.map_preimage (x ≫ s)).symm
  have hiso : LBIso ob.t.PP.L (ob.t.PP.L.pull (𝟙 ob.t.G.left)) :=
    (PolBaseChange.lbIso_refl ob.t.PP.isLB).chartPull (chartPullId _) (chartPullPull _ _ _ rfl)
  refine ⟨{ A := ob.t.G
            ab := ObjDim.isAbelianScheme ob
            dim := hg ▸ ObjDim.smoothOfRelativeDimension ob
            L := ob.t.PP.L
            isLB := ob.t.PP.isLB
            rigid := ObjDim.rigidified
            sym := ObjDim.sym
            ample := ob.ample
            ktriv := ob.ktriv
            pt := pt
            torsion := tors
            bij := fun K _ _ x y hy => ?_
            pairing := fun i i' => ?_
            act := fun c => ob.t.act.act (a c)
            hom := fun c => ob.t.act.hom (a c) },
    ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 ob.t.G)), hiso,
      fun c => (Category.comp_id _).trans (Category.id_comp _).symm, fun i => ?_⟩,
    ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 ob.t.G)), hiso,
      fun c => (Category.comp_id _).trans (Category.id_comp _).symm, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨-, I, -, hI, -⟩ := ob.geom K x _ (hβ K x)
    simp only [hpt, hI]
    exact existsUnique_label l.A_pos (I.ev l.A) (I.add l.A) (I.ker l.A l.A_pos) bas ((I.onto l.A l.A_pos y).1 hy)
  · obtain ⟨c, hc, hcn⟩ := exists_weilIs_root hG (Obj.toPolAV ob) ob.t.cub.t ob.t.cub.isGen l.A (tors i) (tors i')
    have hu : IsUnit ((l.A : ℕ) : Γ(S, ⊤)) := by
      simpa using ((bB.unit l.A l.A_pos).map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).map s.appTop.hom
    have hz : unitS (s ≫ spMap j) b.ζ ^ l.A = 1 := by
      have e := map_unitS (spMap j) (𝟙 _) j (Category.id_comp _) b.ζ
      have e₀ : Units.map j.toMonoidHom b.ζ ^ l.A = 1 := Units.ext (by
        show j b.ζ ^ l.A = 1
        rw [hζ, bB.ζ_prim.pow_eq_one])
      have e₁ : unitS (s ≫ spMap j) b.ζ = Units.map s.appTop.hom.toMonoidHom (unitOn (Units.map j.toMonoidHom b.ζ)) := by
        rw [← e]
        apply Units.ext
        simp [unitS]
        rfl
      rw [e₁, ← map_pow, unitOn, ← map_pow, e₀, map_one, map_one]
    have : c = unitS (s ≫ spMap j) b.ζ ^ Out.stdSymp g i i' := by
      refine root_ext (S := S) hu hcn (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow])
        fun K _ _ x => ?_
      obtain ⟨-, I, hIζ, hI, -⟩ := ob.geom K x _ (hβ K x)
      have h₁ := CommPairing.weilIs_pull hG (ObjDim.isAbelianScheme ob) ob.t.PP.isLB
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) hc
      rw [hpt, hpt, hI, hI] at h₁
      have h₂ := I.isom l.A l.A_pos (bas (Pi.single i 1)) (bas (Pi.single i' 1))
      refine (CommutatorPairing.weilIs_unique hG (ObjDim.isAbelianScheme ob) ob.t.PP.isLB h₁ h₂).trans ?_
      rw [hbas, map_zpow, map_unitS (s ≫ spMap j) x ((Spec.preimage (x ≫ s)).hom.comp j)
        (by rw [← Category.assoc, Geo.Tor.spMap_comp, ← hβ K x]), unitOn, unitOn, map_zpow]
      congr 2
      exact Units.ext (hIζ.trans (congrArg _ hζ.symm))
    exact this ▸ hc
  · have e : (toUnit (Out.baseOver S)).left = 𝟙 S :=
      (Category.comp_id _).symm.trans (Over.w (toUnit (Out.baseOver S)))
    show (ob.etaA _).left ≫ 𝟙 _ = (toUnit (Out.baseOver S)).left ≫ (ob.etaA _).left
    rw [e]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have e : (Spec.preimage (x ≫ s)).hom.comp j = β := by
      have : spMap ((Spec.preimage (x ≫ s)).hom.comp j) = spMap β := by
        rw [Geo.Tor.spMap_comp, ← hβ K x, Category.assoc, hx]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have e₁ : (Spec.preimage (x ≫ s)).hom bB.ρ = β ρ := by rw [← hρ]; exact RingHom.congr_fun e ρ
    have e₂ : (Spec.preimage (x ≫ s)).hom bB.ζ = β b.ζ := by rw [← hζ]; exact RingHom.congr_fun e b.ζ
    have hx' := ob.geom K x _ (hβ K x)
    rw [e₁, e₂] at hx'
    obtain ⟨hd, I, hIζ, hI, -⟩ := hx'
    refine ⟨hd, I, hIζ, fun i => ?_⟩
    exact (Category.comp_id _).trans ((hI _).symm.trans (hpt _ _ i).symm)

end GlobalTheory.ObjTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_structure_pullback : ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s₁ : S ⟶ Sp B) (s' : S' ⟶ Sp o) (s₁' : S' ⟶ Sp B) (t : TObj g k J b s) (c : SiegPre g k ζ s₁) (t' : TObj g k J b s') (c' : SiegPre g k ζ s₁') (f : S' ⟶ S), TSieg bas bas' t c → TMap t' t f → (SiegPB c' c f ↔ TSieg bas bas' t' c') := by
  first | exact @GlobalTheory.ZM.siegPB_iff_tSieg | exact GlobalTheory.ZM.siegPB_iff_tSieg | (intros; apply GlobalTheory.ZM.siegPB_iff_tSieg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_local_on_base_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → (∀ i, Out.Sym (G i) (M i)) → Out.Sym A L := by
  first | exact @GlobalTheory.CoverGlue.sym_of_cover | exact GlobalTheory.CoverGlue.sym_of_cover | (intros; apply GlobalTheory.CoverGlue.sym_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_fieldExtension_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  first | exact @GlobalTheory.weilIs_fieldExt_iff | exact GlobalTheory.weilIs_fieldExt_iff | (intros; apply GlobalTheory.weilIs_fieldExt_iff <;> assumption)
end

