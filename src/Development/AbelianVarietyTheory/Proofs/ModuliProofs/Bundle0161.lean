import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueComapEqVanishingIdeal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PtHomEqPtHomIffProportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfComplexPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0153
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaDvr

theorem app_eq_zero_of_not_mem {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [Smooth G.hom]
    {U : G.left.Opens} (a : Γ(G.left, U))
    (h : ∀ x ∈ G.left.basicOpen a, G.hom x ≠ IsLocalRing.closedPoint V) :
    ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom a = 0 := by

  have hk : _root_.IsReduced (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := by
    rw [zero_add, pow_one]
    infer_instance
  have : IsReduced (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0))

  have hpt : ∀ y : ↥(pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)),
      G.hom (pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0) y) = IsLocalRing.closedPoint V := by
    intro y
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · exact (Ideal.ne_top_iff_one _).mpr (PrimeSpectrum.isPrime _).one_notMem
    · intro r hr
      have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [zero_add, pow_one]; exact hr)
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r ∈
        ((pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y).asIdeal
      rw [h0]
      exact Ideal.zero_mem _

  have hbot : (fstG (IsLocalRing.maximalIdeal V) 0 G).left ⁻¹ᵁ G.left.basicOpen a = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => (h _ hy (hpt y)).elim
  rw [Scheme.preimage_basicOpen] at hbot
  exact (@basicOpen_eq_bot_iff _ this _ _).mp hbot

private lemma secIsMul_trans' {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB Y} {a b : R} {σ τ τ' : LB.Sec L} (h : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ)
    (h' : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p b τ τ') : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p (a * b) σ τ' := by
  intro k
  rw [h k, h' k, ← _root_.mul_assoc]
  congr 1
  simp only [resTop, scal, map_mul]

private lemma gs_id_eq_germ_moduli {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)) (z : X) (hz : z ∈ U) :
    gs (𝟙 X) z U a = (X.presheaf.germ U z hz).hom a := by
  unfold gs
  rw [dif_pos (show (𝟙 X) z ∈ U from hz)]
  rfl

theorem exists_sec_unit_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left)
    (hN : N.IsLB) (s : LB.Sec (N.pull (pullback.fst G.hom (jK V)))) (j) (hj : s.f j ≠ 0) :
    ∃ (θ : LB.Sec N) (k : N.ι), ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hflat : (algebraMap V (FractionRing V)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (FractionRing V) (nonZeroDivisors V))
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  have hpb : IsPullback (pullback.fst G.hom (jK V)) (pullback.snd G.hom (jK V)) G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) := IsPullback.of_hasPullback _ _

  obtain ⟨n, c, u, hu⟩ := GlobalTheory.FlatSec.exists_comb_of_flat V (FractionRing V) _ hflat G.left G.hom _
    (pullback.fst G.hom (jK V)) _ hpb N hN s
  have hne : ∃ i k, (u i).f k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hj
    apply TopCat.Presheaf.section_ext (pullback G.hom (jK V)).sheaf
    intro z hz
    have hj' : j = fun _ => j PUnit.unit := funext fun x => by cases x; rfl
    have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := by
      rw [hj'] at hz
      simpa [LB.pull, LB.LinComb, LB.wchart] using hz
    have h1 := hu z (j PUnit.unit) hz'
    rw [← hj'] at h1
    rw [gs_id_eq_germ_moduli _ _ z hz] at h1
    refine Eq.trans ?_ (map_zero _).symm
    change ((pullback G.hom (jK V)).presheaf.germ _ z hz).hom (s.f j) = 0
    rw [h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcon i (j PUnit.unit)]
    simp [gs]
  obtain ⟨i, k₀, hk₀⟩ := hne
  set θ₀ := u i

  have hjac : IsLocalRing.maximalIdeal V ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hex : ∃ m, ∃ k, ((fstG (IsLocalRing.maximalIdeal V) m G).left.app _).hom (θ₀.f k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk₀ ((GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings V _ hjac G).1 N hN θ₀ hcon k₀)
  classical

  have hunit : ∀ (θ : LB.Sec N) (k : N.ι), ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (θ.f k) ≠ 0 →
      ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
    intro θ k hθ
    by_contra hcon
    push Not at hcon
    exact hθ (app_eq_zero_of_not_mem G (θ.f k) hcon)

  obtain ⟨k₁, hk₁⟩ := Nat.find_spec hex
  rcases hm : Nat.find hex with _ | e
  · rw [hm] at hk₁
    obtain ⟨x, hx, hxc⟩ := hunit θ₀ k₁ hk₁
    exact ⟨θ₀, k₁, x, hx, hxc⟩
  · have hlt : ¬ ∃ k, ((fstG (IsLocalRing.maximalIdeal V) e G).left.app _).hom (θ₀.f k) ≠ 0 :=
      Nat.find_min hex (by omega)
    push Not at hlt
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ e).1 hlt
    have hτ0 : ∃ k, ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (τ.f k) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨τ', hτ'⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N τ 0).1 hcon
      have h2 := secIsMul_trans' G.hom hτ hτ'
      rw [← pow_add] at h2
      have h3 := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ (e + 1)).2 ⟨τ', h2⟩
      rw [hm] at hk₁
      exact hk₁ (h3 k₁)
    obtain ⟨k, hk⟩ := hτ0
    obtain ⟨x, hx, hxc⟩ := hunit τ k hk
    exact ⟨τ, k, x, hx, hxc⟩

theorem thetaNZ_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)), GlobalTheory.LN.PolAt t (jK V) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro hL hL2 E _ _ _ H V _ _ _ t ht
  obtain ⟨A, oA, gen, -, hiso, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt hL hL2 E H V t ht
  have hsa := t.4
  have : Smooth t.G.hom := hsa.2
  have : IsSeparated t.G.hom := hsa.3
  have : QuasiCompact t.G.hom := hsa.4
  have : GeometricallyConnected t.G.hom := hsa.5
  have hLt : t.PP.L.IsLB := t.PP.3

  have hP := GlobalTheory.PushInv.pushInvertible_any hL2.1 hL.1 _ A
  obtain ⟨W, hxW, θ, hθ, -, hnz⟩ := hP (IsLocalRing.closedPoint (FractionRing V))
  obtain ⟨g, i, -, hg⟩ := hnz _ hxW
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hO : ⊤ ≤ gen.hom.left ⁻¹ᵁ (A.A.hom ⁻¹ᵁ W) := by
    intro y _
    change A.A.hom (gen.hom.left y) ∈ W
    rwa [Subsingleton.elim (A.A.hom (gen.hom.left y)) (IsLocalRing.closedPoint (FractionRing V))]
  obtain ⟨θ', hθ'⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (LB.isLB_pull hLt _) gen.hom.left w hw hO θ hθ
  have hgy : gen.hom.left (gen.inv.left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, gen.inv_hom_id, Over.id_left]
    rfl
  obtain ⟨k, hk⟩ := hθ' (gen.inv.left g) i (by rwa [hgy])
  have hk0 : θ'.f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk

  obtain ⟨σ, l, x, hx, hxc⟩ := exists_sec_unit_closed_fibre V t.G t.PP.L hLt θ' k hk0

  refine ⟨σ, fun y => ?_⟩
  have hy : y ⤳ t.G.hom x := hxc ▸ IsLocalRing.specializes_closedPoint y
  obtain ⟨x', hx', hx'y⟩ := Flat.generalizingMap t.G.hom hy
  exact ⟨x', l, hx'y, hx'.mem_open (t.G.left.basicOpen (σ.f l)).isOpen hx⟩

end GlobalTheory.ThetaDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueDescentAutomorphismInvariantMorphism
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.InvariantMorDescent

theorem exists_equalizer_ideal {Z Y S : Scheme.{0}} (z : Y ⟶ S) [IsSeparated z] (a b : Z ⟶ Y)
    (h : a ≫ z = b ≫ z) :
    ∃ I : Z.IdealSheafData, ∀ (T : Scheme.{0}) (t : T ⟶ Z), I ≤ t.ker ↔ t ≫ a = t ≫ b := by
  let i := pullback.fst (pullback.lift a b h) (pullback.diagonal z)
  have hi : i ≫ a = i ≫ b := by
    have c : i ≫ _ = _ := pullback.condition (f := pullback.lift a b h) (g := pullback.diagonal z)
    have c₁ := congrArg (· ≫ pullback.fst z z) c
    have c₂ := congrArg (· ≫ pullback.snd z z) c
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd] at c₁ c₂
    exact c₁.trans c₂.symm
  refine ⟨i.ker, fun T t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · rw [← IsClosedImmersion.lift_fac i t ht, Category.assoc, Category.assoc, hi]
  · have e : t ≫ pullback.lift a b h = (t ≫ a) ≫ pullback.diagonal z := by
      apply pullback.hom_ext
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd, ht]
    rw [← pullback.lift_fst t (t ≫ a) e]
    exact Scheme.Hom.le_ker_comp _ _

theorem fst_comp_eq_snd_comp {K L : Type} [Field K] [Field L] [Algebra K L] {G : Type*}
    (s : G → L →ₐ[K] L) (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    {X X' Y S : Scheme.{0}} {p : X ⟶ Spec (.of K)} {q : X' ⟶ Spec (.of L)} {π : X' ⟶ X}
    (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (z : Y ⟶ S) [IsSeparated z] (f : X' ⟶ Y) (u : X ⟶ S) (hu : f ≫ z = π ≫ u)
    (hf : ∀ g, GaloisDescent.twist H (s g) ≫ f = f) :
    pullback.fst π π ≫ f = pullback.snd π π ≫ f := by
  have hp : IsPullback (pullback.fst π π) (pullback.snd π π ≫ q) (π ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsPullback.of_hasPullback π π).paste_vert H
  obtain ⟨I, hI⟩ := exists_equalizer_ideal z (pullback.fst π π ≫ f) (pullback.snd π π ≫ f) (by
    rw [Category.assoc, Category.assoc, hu, pullback.condition_assoc])
  have h₂ : ∀ g, GaloisDescent.twist hp (s g) ≫ pullback.snd π π =
      pullback.snd π π ≫ GaloisDescent.twist H (s g) := fun g => by
    apply H.hom_ext
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst, ← pullback.condition,
        GaloisDescent.twist_fst_assoc]
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_snd, GaloisDescent.twist_snd,
        Category.assoc]
  obtain ⟨J, hJ, -⟩ := (GaloisDescent.idealSheaf_stable_iff_exists_comap hp s hs I).1 fun g => by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
    refine (hI _ _).2 ?_
    rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst_assoc, reassoc_of% (h₂ g), hf]
    exact (hI _ _).1 I.ker_subschemeι.ge
  have h₃ : I ≤ (pullback.diagonal π).ker := (hI _ _).2 (by simp)
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le, ← hJ,
    ← Scheme.IdealSheafData.comap_comp, pullback.diagonal_fst,
    Scheme.IdealSheafData.comap_id, le_bot_iff] at h₃
  rw [h₃, Scheme.IdealSheafData.comap_bot] at hJ
  simpa using (hI _ (𝟙 _)).1 (hJ ▸ bot_le)

theorem existsUnique_desc : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [IsAlgClosed C] [Algebra K C] (S : Scheme.{0}) (b : Sp K ⟶ S) (X Y : Over S), IsSeparated Y.hom → ∀ κ : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk b, κ.left = spMap (algebraMap K C) → ∀ f : Over.mk (spMap (algebraMap K C) ≫ b) ⊗ X ⟶ Y, (∀ (σ : C ≃ₐ[K] C) (s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b)), s.left = spMap (σ : C →+* C) → s ▷ X ≫ f = f) → ∃! g : Over.mk b ⊗ X ⟶ Y, κ ▷ X ≫ g = f := by
  intro K C _ _ _ _ _ S b X Y hY κ hκ f hf
  have f₁ : Flat κ.left := by
    rw [hκ]
    change Flat (spMap (algebraMap K C))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective κ.left := ⟨fun y =>
    ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have f₃ : QuasiCompact κ.left := by
    rw [hκ]
    exact inferInstanceAs (QuasiCompact (spMap (algebraMap K C)))
  have H : IsPullback (κ ▷ X).left (fst _ X).left (fst (Over.mk b) X).left
      (Spec.map (CommRingCat.ofHom (algebraMap K C))) := by
    have := (SemiRigid.isPullback_whiskerRight κ X).flip
    rw [hκ] at this
    exact this
  have key := fst_comp_eq_snd_comp (fun σ : C ≃ₐ[K] C => σ.toAlgHom)
    GaloisDescent.mem_range_algebraMap_of_forall_algEquiv H Y.hom f.left (Over.mk b ⊗ X).hom
    ((Over.w f).trans (Over.w (κ ▷ X)).symm) fun σ => by
      have hσ : spMap (σ : C →+* C) ≫ spMap (algebraMap K C) = spMap (algebraMap K C) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact σ.toAlgHom.comp_algebraMap
      let s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b) :=
        Over.homMk (spMap (σ : C →+* C)) (by
          change spMap (σ : C →+* C) ≫ spMap (algebraMap K C) ≫ b = spMap (algebraMap K C) ≫ b
          rw [reassoc_of% hσ])
      have hsκ : s ≫ κ = κ := Over.OverMorphism.ext (by
        rw [Over.comp_left, hκ]; exact hσ)
      have e : GaloisDescent.twist H σ.toAlgHom = (s ▷ X).left := by
        apply H.hom_ext
        · rw [GaloisDescent.twist_fst, ← Over.comp_left, ← comp_whiskerRight, hsκ]
        · rw [GaloisDescent.twist_snd]
          exact congrArg (·.left) (whiskerRight_fst s X).symm
      rw [e]
      exact congrArg (·.left) (hf σ s rfl)
  obtain ⟨g, hg⟩ := SemiRigid.exists_desc (κ ▷ X) f fun Z a c h => by
    have h' : a.left ≫ (κ ▷ X).left = c.left ≫ (κ ▷ X).left := congrArg (·.left) h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← pullback.lift_fst a.left c.left h', Category.assoc, key,
      pullback.lift_snd_assoc]
  have := SemiRigid.epi_of_fpqc (κ ▷ X)
  exact ⟨g, hg, fun g' hg' => (cancel_epi (κ ▷ X)).1 (hg'.trans hg.symm)⟩

end GlobalTheory.InvariantMorDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnimodularSolTwoTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models.EllipticModel

open GlobalTheory.WeierstrassCurve

noncomputable def curve : _root_.WeierstrassCurve ℤ_[3] := ⟨0, 0, 0, -1, 0⟩

theorem isUnit_curve_Δ : IsUnit curve.Δ := by
  have h : curve.Δ = ((64 : ℤ) : ℤ_[3]) := by
    simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  rw [h, PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
  revert hlt
  norm_num

theorem isUnimodularSol_origin : IsUnimodularSol (curve.map (RingHom.id _)) ![0, 1, 0] := by
  refine ⟨?_, (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨1, rfl⟩)⟩
  rw [WeierstrassCurve.Projective.equation_iff]
  simp

theorem isUnimodularSol_twoTorsion : IsUnimodularSol (curve.map (RingHom.id _)) ![0, 0, 1] := by
  refine ⟨?_, (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨2, rfl⟩)⟩
  rw [WeierstrassCurve.Projective.equation_iff]
  simp [curve]

theorem not_mono_toSpec : ¬ Mono (toSpec curve) := by
  intro hm
  have h : ptHom curve (RingHom.id _) _ isUnimodularSol_origin =
      ptHom curve (RingHom.id _) _ isUnimodularSol_twoTorsion := by
    rw [← cancel_mono (toSpec curve), ptHom_toSpec, ptHom_toSpec]
  have h' := (GlobalTheory.AddLaw.ptHom_eq_ptHom_iff_proportional _ curve _ _ _ _ _ _).1 h 1 2
  simp at h'

theorem not_isIso_tensorTriple {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}}
    (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (h : ¬ Mono A.hom) :
    ¬ IsIso (tensorTriple H A hA).G.hom := by
  intro hi
  obtain ⟨i, r, hir⟩ := exists_retract_tensorTriple (H := H) A hA
  have e : i.left ≫ r.left = 𝟙 A.left := by rw [← Over.comp_left, hir, Over.id_left]
  have : Mono i.left := mono_of_mono_fac e
  exact h (Over.w i ▸ inferInstance)

end GlobalTheory.Models.EllipticModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SameFactor

variable {A : Over (Sp ℂ)} [GrpObj A] {M M' : LB A.left} {g : ℕ}

theorem valAt'_div_g {X : Scheme.{0}} (M M' : LB X) (x : Sp ℂ ⟶ X) (p q : (LB.div M' M).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.div M' M).U p ⊓ (LB.div M' M).U q)) :
    valAt' x ((LB.div M' M).U p ⊓ (LB.div M' M).U q) ((LB.div M' M).g p q).val =
      valAt' x (M'.U p.1 ⊓ M'.U q.1) (M'.g p.1 q.1).val * (valAt' x (M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2).val)⁻¹ := by
  dsimp only [LB.div] at h ⊢
  rw [Units.val_mul, valAt'_mul, valAt'_units_inv x h, GlobalTheory.HolSecAlg.val_res_unit x _ _ h,
    GlobalTheory.HolSecAlg.val_res_unit x _ _ h]

def divUnif (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex) : HolUnif A (LB.div M' M) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun p z => u'.fr p.1 z * (u.fr p.2 z)⁻¹
  fr_hol := fun p => by
    have h1 := u'.fr_hol p.1
    rw [hex] at h1
    refine DifferentiableOn.mul (h1.mono fun z hz => ?_)
      (DifferentiableOn.inv ((u.fr_hol p.2).mono fun z hz => ?_) fun z hz => u.fr_ne _ _ ?_)
    · exact ((top_le_preimage_inf _ _ _).1 hz).1
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
  fr_ne := fun p z hz => by
    obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    exact mul_ne_zero (u'.fr_ne _ _ (by rw [hex]; exact h1)) (inv_ne_zero (u.fr_ne _ _ h2))
  fr_compat := fun p q z hz => by
    obtain ⟨hp, hq⟩ := (top_le_preimage_inf _ _ _).1 hz
    obtain ⟨hp1, hp2⟩ := (top_le_preimage_inf _ _ _).1 hp
    obtain ⟨hq1, hq2⟩ := (top_le_preimage_inf _ _ _).1 hq
    have e1 := u'.fr_compat p.1 q.1 z (by rw [hex]; exact (top_le_preimage_inf _ _ _).2 ⟨hp1, hq1⟩)
    rw [hex] at e1
    have e2 := u.fr_compat p.2 q.2 z ((top_le_preimage_inf _ _ _).2 ⟨hp2, hq2⟩)
    rw [valAt'_div_g M M' _ p q hz, e1, e2, mul_inv]
    ring

theorem exists_gen_of_isFn [LocallyOfFiniteType A.hom] (u : HolUnif A M g) (s : M.Sec) (θ : (Fin g → ℂ) → ℂ)
    (hs : u.IsFn s θ) (hθ : ∀ z, θ z ≠ 0) : ∃ t : LB.Gen M, t.IsGen := by

  have hunit : ∀ i, IsUnit (s.f i) := fun i =>
    GlobalTheory.ThetaBundleSym.isUnit_of_complex_points u.ex_onto (s.f i) fun z hz => by
      rw [hs i z hz]
      exact mul_ne_zero (hθ z) (u.fr_ne i z hz)
  refine ⟨⟨fun i => (hunit i).unit⟩, fun i j => Units.ext ?_⟩
  rw [Units.val_mul]
  exact s.compat i j

end SameFactor

theorem lbIso_of_same_factor : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (M M' : LB P.A.left) (u : HolUnif P.A M P.g) (u' : HolUnif P.A M' P.g), M.IsLB → M'.IsLB → u'.ex = u.ex → (∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ M'.U j → u.fr i z * u'.fr j (z + l) = u.fr i (z + l) * u'.fr j z) → LBIso M M' := by
  intro hL hL2 hTh hU P M M' u u' hM hM' hex hfac
  have : LocallyOfFiniteType P.A.hom := by
    have := P.isAb.proper
    infer_instance

  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_algebraic_section_of_holomorphic_theta hL hL2 hTh hU P (LB.div M' M) (SameFactor.divUnif u u' hex) (fun _ => 1)
    (LB.isLB_div hM' hM) (differentiable_const 1) (by
      intro l p z hz
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have hl : u.ex (z + l) = u.ex z := GlobalTheory.HolSecAlg.ex_add_lattice u z l.2
      have n0 : u.fr p.2 z ≠ 0 := u.fr_ne _ _ h2
      have n1 : u.fr p.2 (z + l) ≠ 0 := u.fr_ne _ _ (by rw [hl]; exact h2)
      have key := hfac l p.2 p.1 z h2 h1
      show (1 : ℂ) * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (u'.fr p.1 z * (u.fr p.2 z)⁻¹)
      rw [_root_.one_mul, _root_.one_mul, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff n1 n0]
      linear_combination key)
  obtain ⟨t, ht⟩ := SameFactor.exists_gen_of_isFn _ s (fun _ => 1) hs fun _ => one_ne_zero
  exact ⟨t, ht⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDvdFormOfCubWeilOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.Coisotropic

theorem eq_one_of_unitOn_eq_one {R : Type} [CommRing R] {u : Rˣ} (h : unitOn u = 1) : u = 1 := by
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact congrArg Units.val h

theorem level_dvd_form_of_cubWeil_one : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ∀ (K : Type) [Field K] [IsAlgClosed K] (u : Sp K ⟶ U) (a a' : D.La) (p p' : Over.mk (u ≫ j) ⟶ t.G), p.left = u ≫ (o.etaA a).left ≫ μ₀.φ → p'.left = u ≫ (o.etaA a').left ≫ μ₀.φ → CubWeil t.cub l.A p p' 1 → (l.A : ℤ) ∣ D.EF a a' := by
  intro hL E _ _ _ H D l B _ b X U j s o t μ₀ K _ _ u a a' p p' hp hp' h
  have hβ : u ≫ s = spMap (Spec.preimage (u ≫ s)).hom := (Spec.map_preimage (u ≫ s)).symm
  obtain ⟨-, I, -, hI, -⟩ := o.geom K u _ hβ
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have kill : ∀ c, I.ev l.A c ^ l.A = 1 := fun c => (I.onto l.A l.A_pos _).2 ⟨c, rfl⟩
  have h₁ : CubWeil o.t.cub l.A (I.ev l.A a) (I.ev l.A a') (unitOn (I.ζ l.A ^ D.EF a a')) :=
    (cubWeil_iff_weilIs hL.globalFns hA (kill a) (kill a') _).2 (I.isom l.A l.A_pos a a')
  have h₂ := GlobalTheory.T.cubicalBundlePairing_compatible_pullback X U j t.G o.t.G μ₀.cm μ₀.cart.1.w
    (fun T x y => Over.OverMorphism.ext (μ₀.cart.2 T x y _ _ rfl rfl).symm) _ _ _ _ μ₀.lin l.A _ _ _ _ h₁
  have e : ∀ (c : D.La) (q : Over.mk (u ≫ j) ⟶ t.G), q.left = u ≫ (o.etaA c).left ≫ μ₀.φ →
      Out.toBase μ₀.cart.1.w (I.ev l.A c) = q := fun c q hq => Over.OverMorphism.ext (by
    rw [hq, ← hI c]
    show ((toUnit (Over.mk u)).left ≫ (o.etaA c).left) ≫ μ₀.φ = _
    rw [Category.assoc]
    rfl)
  rw [e a p hp, e a' p' hp'] at h₂
  exact ((I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd _).1 (eq_one_of_unitOn_eq_one (h₂.unique h))

end GlobalTheory.Coisotropic
end

