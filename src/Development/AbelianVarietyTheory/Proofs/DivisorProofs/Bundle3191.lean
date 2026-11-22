import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicFormEqRationalPhaseKernelSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3152
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0087
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0010
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddedPartPointsOverClosedProjPointClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibClosed

theorem closed_in_preimage {F X P B : Scheme.{0}} (p : F ⟶ B) (q : B ⟶ P) (φ : F ⟶ X) (g : X ⟶ P) [IsProper p]
    [IsPreimmersion q] [IsSeparated g] (h : φ ≫ g = p ≫ q) :
    ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' Set.range q = Set.range φ := by
  let m : F ⟶ pullback g q := pullback.lift φ p h
  have hm : m ≫ pullback.snd g q = p := pullback.lift_snd _ _ _
  have : IsProper (m ≫ pullback.snd g q) := by rw [hm]; infer_instance
  have : IsProper m := IsProper.of_comp m (pullback.snd g q)
  have hcl : IsClosed (Set.range m) := m.isClosedMap.isClosed_range
  have hemb : Topology.IsEmbedding (pullback.fst g q) := (pullback.fst g q).isEmbedding
  obtain ⟨C, hC, hCe⟩ := hemb.isInducing.isClosed_iff.1 hcl
  refine ⟨C, hC, ?_⟩
  rw [← Scheme.Pullback.range_fst, ← Set.image_preimage_eq_inter_range, hCe, ← Set.range_comp]
  congr 1
  ext x
  show (m ≫ pullback.fst g q) x = φ x
  rw [pullback.lift_fst]

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

theorem exists_redFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    [IsProper π] : ∃ (T : Scheme.{0}) (t : T ⟶ S) (k : T ⟶ Sp (ResidueField R)), IsLocallyNoetherian T ∧ IsReduced T ∧
      IsProper k ∧ t ≫ π = k ≫ spMap (residue R) ∧ Set.range t = π ⁻¹' {closedPoint R} := by
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  let Z : TopologicalSpace.Closeds S := ⟨π ⁻¹' {closedPoint R}, hcp.preimage π.continuous⟩
  let Z₀ : TopologicalSpace.Closeds (Sp R) := ⟨{closedPoint R}, hcp⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let t := I.subschemeι
  have hrt : Set.range t = π ⁻¹' {closedPoint R} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  have hr : Set.range (t ≫ π) ⊆ (Z₀ : Set (Sp R)) := by
    rintro _ ⟨x, rfl⟩
    have : t x ∈ Set.range t := ⟨x, rfl⟩
    rw [hrt] at this
    exact this
  have h1 : Scheme.IdealSheafData.vanishingIdeal Z₀ ≤ (t ≫ π).ker :=
    GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker (t ≫ π) Z₀ hr
  have h2 : (spMap (residue R)).ker ≤ Scheme.IdealSheafData.vanishingIdeal Z₀ := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    have hx' : x = closedPoint R := hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]
    refine subset_closure ⟨closedPoint (ResidueField R), ?_⟩
    rw [hx']
    exact IsLocalRing.comap_closedPoint (residue R)
  let k := IsClosedImmersion.lift (spMap (residue R)) (t ≫ π) (h2.trans h1)
  have hk : k ≫ spMap (residue R) = t ≫ π := IsClosedImmersion.lift_fac _ _ _
  have : IsProper (k ≫ spMap (residue R)) := by rw [hk]; infer_instance
  have : IsProper k := IsProper.of_comp k (spMap (residue R))
  exact ⟨I.subscheme, t, k, inferInstance, inferInstance, inferInstance, hk.symm, hrt⟩

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

theorem ap {A B : Scheme.{0}} {f f' : A ⟶ B} (h : f = f') (x : A) : f x = f' x := h ▸ rfl

theorem range_inter_fibre_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (H' : E.H.toScheme.Opens) (X : Scheme.{0}) (o : H'.toScheme ⟶ X) (g : X ⟶ PSpace R E.N), IsSeparated g → o ≫ g = H'.ι ≫ E.f → (∀ z : E.H.toScheme, π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ H') → ∀ w : PSpace R E.N, PSpace.str R E.N w = closedPoint R → ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' {w} = Set.range o ∩ g ⁻¹' {w} := by
  intro R _ _ _ S π hπ G' _ hG E H' X o g hg hog hH' w hw
  haveI := hπ
  haveI := hg
  obtain ⟨T, t, k, hTn, hTr, hk, htk, hrt⟩ := exists_redFibre R S π
  obtain ⟨e, l, -, hl, hlf⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t k hTn hTr htk
  have hover : ∀ p, π (G'.hom (E.H.ι (l p))) = closedPoint R := by
    intro p
    have h1 : E.H.ι (l p) = pullback.fst G'.hom t p := by
      rw [← ap hl p, Scheme.Hom.comp_apply]
    have h2 : G'.hom (pullback.fst G'.hom t p) = t (pullback.snd G'.hom t p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have h3 : t (pullback.snd G'.hom t p) ∈ Set.range t := ⟨_, rfl⟩
    rw [hrt] at h3
    rw [h1, h2]; exact h3
  have hrl : Set.range l ⊆ Set.range H'.ι := by
    rintro _ ⟨p, rfl⟩; rw [Scheme.Opens.range_ι]; exact hH' _ (hover p)
  let l' := IsOpenImmersion.lift H'.ι l hrl
  have hl' : l' ≫ H'.ι = l := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ z : H'.toScheme, g (o z) = w →
      ∃ p, l' p = z ∧ E.j (pullback.fst E.Y.hom k (e.hom p)) = w := by
    intro z hz
    have hfz : E.f (H'.ι z) = w := by
      rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hog]
    have hcl : π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R := by
      have := ap E.f_over (H'.ι z)
      simp only [Scheme.Hom.comp_apply] at this
      rw [← this, hfz, hw]
    obtain ⟨p, hp⟩ : E.H.ι (H'.ι z) ∈ Set.range (pullback.fst G'.hom t) := by
      rw [Scheme.Pullback.range_fst]
      show G'.hom _ ∈ Set.range t
      rw [hrt]; exact hcl
    have hlp : l p = H'.ι z := E.H.ι.isOpenEmbedding.injective (by
      rw [← hp, ← ap hl p, Scheme.Hom.comp_apply])
    refine ⟨p, H'.ι.isOpenEmbedding.injective (by rw [← hlp, ← ap hl' p, Scheme.Hom.comp_apply]), ?_⟩
    rw [← hfz, ← hlp]
    have h := ap hlf p
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  by_cases hy : ∃ y, E.j y = w
  · obtain ⟨y, rfl⟩ := hy
    haveI := E.imm
    let F := pullback (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y)
    let φ : F ⟶ X := pullback.fst _ _ ≫ e.inv ≫ l' ≫ o
    have hφ : φ ≫ g = pullback.snd _ _ ≫ (E.Y.left.fromSpecResidueField y ≫ E.j) := by
      simp only [φ, Category.assoc, hog]
      rw [reassoc_of% hl', hlf, Iso.inv_hom_id_assoc, pullback.condition_assoc]
    obtain ⟨C, hC, hCe⟩ := closed_in_preimage (pullback.snd (pullback.fst E.Y.hom k)
      (E.Y.left.fromSpecResidueField y)) _ φ g hφ
    have hrange : Set.range (E.Y.left.fromSpecResidueField y ≫ E.j) = {E.j y} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩
        have : E.Y.left.fromSpecResidueField y a ∈ Set.range (E.Y.left.fromSpecResidueField y) := ⟨a, rfl⟩
        rw [Scheme.range_fromSpecResidueField] at this
        rw [this]
      · rintro rfl
        have : y ∈ Set.range (E.Y.left.fromSpecResidueField y) := by
          rw [Scheme.range_fromSpecResidueField]; rfl
        obtain ⟨a, ha⟩ := this
        exact ⟨a, by rw [ha]⟩
    refine ⟨C, hC, ?_⟩
    rw [← hrange, hCe]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨(pullback.fst _ _ ≫ e.inv ≫ l') a, ?_⟩, ?_⟩
      · show o _ = φ a
        simp only [φ, Scheme.Hom.comp_apply]
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hφ]
        exact ⟨pullback.snd (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y) a,
          (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      rw [hrange] at hz
      obtain ⟨p, hp, hpj⟩ := key z hz
      have hyp : pullback.fst E.Y.hom k (e.hom p) = y := E.j.isEmbedding.injective hpj
      obtain ⟨a, ha⟩ : e.hom p ∈ Set.range (pullback.fst (pullback.fst E.Y.hom k)
          (E.Y.left.fromSpecResidueField y)) := by
        rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
        exact hyp
      refine ⟨a, ?_⟩
      simp only [φ, Scheme.Hom.comp_apply]
      have h := ap e.hom_inv_id p
      simp only [Scheme.Hom.comp_apply] at h
      rw [ha, h]
      exact congrArg o hp
  · refine ⟨∅, isClosed_empty, ?_⟩
    ext x
    simp only [Set.empty_inter, Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage,
      Set.mem_singleton_iff, false_iff, not_and]
    rintro ⟨z, rfl⟩ hz
    obtain ⟨p, -, hpj⟩ := key z hz
    exact hy ⟨_, hpj⟩

end GlobalTheory.Mum.FibClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfEqOnRapoportUnitSix
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem eq_zero_of_forall_away {R : Type} [CommRing R] (d : R)
    (h : ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧ algebraMap R (Localization.Away f) d = 0) : d = 0 := by
  set I : Submodule R R := (Submodule.span R {d}).annihilator
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa using (Submodule.mem_annihilator_span_singleton d 1).1 h1
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨f, hf, hfd⟩ := h ⟨m, hm.isPrime⟩
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hfd
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hfd
    have : f ^ n ∈ I := (Submodule.mem_annihilator_span_singleton d _).2 (by simpa [smul_eq_mul] using hn)
    exact (hf (hm.isPrime.mem_of_pow_mem n (hle this))).elim

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem Rule.agreeOn_of_isRapoport {R₀ : Type} [CommRing R₀] {k : ℕ} (s t : Rule (unitObj 𝔠 6) R₀ k)
    (hst : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), X.IsRapoport →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ)
    {A : Type} [CommRing A] (Y : Obj F 𝔠 (Sp A)) (hY : Y.IsRapoport) : s.AgreeOn t Y :=
  fun B _ _ σ Y' _ hY' h δ ↦ hst B Y' h (hY'.isRapoport σ hY) δ

theorem isRapoport_of_le_rapLocus {M : Scheme.{0}} (U : Obj F 𝔠 M) (V : M.Opens) (hV : (V : Set M) = U.rapLocus)
    (W : M.Opens) (hW : IsAffineOpen W) (hle : W ≤ V) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left)
    (hY : Y.IsPullBy U hW.fromSpec φ) : Y.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun x K _ t hx Z ψ hZ ↦ ?_
  have hmem : hW.fromSpec x ∈ U.rapLocus := by
    rw [← hV]; apply hle; show hW.fromSpec x ∈ (W : Set M); rw [← hW.range_fromSpec]; exact ⟨x, rfl⟩
  refine hmem K (t ≫ hW.fromSpec) ?_ Z (ψ ≫ φ) (hZ.comp hY)
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

theorem isUnit_six_of_away {M : Scheme.{0}} (sM : M ⟶ Sp (Localization.Away (12 : ℤ))) (W : M.Opens) :
    IsUnit ((6 : ℕ) : Γ(M, W)) := by
  have h12 : IsUnit (algebraMap ℤ (Localization.Away (12 : ℤ)) 12) := IsLocalization.Away.algebraMap_isUnit _
  have h6 : IsUnit ((6 : ℕ) : Localization.Away (12 : ℤ)) := by
    have : algebraMap ℤ (Localization.Away (12 : ℤ)) 12 = ((6 : ℕ) : Localization.Away (12 : ℤ)) * 2 := by
      simp; norm_num
    rw [this] at h12
    exact isUnit_of_mul_isUnit_left h12
  let g : Localization.Away (12 : ℤ) →+* Γ(M, W) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (12 : ℤ)))).inv ≫ sM.appTop ≫
      M.presheaf.map (homOfLE le_top).op).hom
  have := h6.map g
  rwa [map_natCast] at this

end GlobalTheory.RealMult

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_on_rapoport_unit_six : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
  (R₀ : Type) [CommRing R₀] (k : ℕ) (s t : Rule (unitObj 𝔠 6) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), X.IsRapoport →
    ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  intro hDP F _ _ _ 𝔠 R₀ _ k s t hst
  obtain ⟨M, sM, U, αU, hfine, -, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 12 (by norm_num)
  have hchart : ∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ → Nonempty Y.DetGen → s.AgreeOn t Y := by
    intro W hW Y φ hY hgen
    exact GlobalTheory.T.determinant_generator_rule_base_change F 𝔠 R₀ k s t Γ(M, W) Y hgen
      (GlobalTheory.T.flat_normal_fibers_open_extension F 𝔠 R₀ k s t 12 M sM U V hflat hnorm hcod W hW
        (fun W' hW' hle Y' φ' hY' ↦ Rule.agreeOn_of_isRapoport s t hst Y'
          (isRapoport_of_le_rapLocus U V hV W' hW' (hle.trans inf_le_right) Y' φ' hY')) Y φ hY)
      (isUnit_six_of_away sM W)
  apply GlobalTheory.T.modular_rule_ext_of_level_twelve F 𝔠 R₀ k s t
  intro R _ _ X h6 ⟨α⟩ δ
  have h6' : IsUnit (6 : R) := by exact_mod_cast h6
  have h2 : IsUnit (2 : R) := isUnit_of_mul_isUnit_left (y := (3 : R)) (by norm_num; exact h6')
  have h12 : IsUnit ((Int.castRingHom R) 12) := by
    have : (Int.castRingHom R) 12 = 6 * 2 := by simp; norm_num
    rw [this]; exact h6'.mul h2
  let τ : Localization.Away (12 : ℤ) →+* R := IsLocalization.Away.lift (12 : ℤ) h12
  obtain ⟨b, -, φ, hφ, -⟩ := (hfine (Sp R) (spMap τ) X α).exists
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_away
  intro p
  obtain ⟨W, hW, hy, Y, ψ, hY, hgen⟩ := GlobalTheory.T.local_affine_determinant_generator F 𝔠 M U (b p)
  obtain ⟨f, g, hp, hg⟩ := GlobalTheory.T.affine_open_local_factorization M W hW R b p hy
  obtain ⟨Xf, φf, hXf⟩ := Obj.exists_isPullBy X (spMap (algebraMap R (Localization.Away f)))
  obtain ⟨δf, hδf, -⟩ := hXf.existsUnique_detGen _ δ
  have hXfU := hXf.comp hφ
  rw [← hg] at hXfU
  obtain ⟨χ, hχ, -⟩ := hXfU.cancel hY
  have h6f : IsUnit ((6 : ℕ) : Localization.Away f) := by
    have := h6.map (algebraMap R (Localization.Away f))
    rwa [map_natCast] at this
  refine ⟨f, hp, ?_⟩
  have e1 := s.baseChange R (Localization.Away f) (IsScalarTower.toAlgHom R₀ R _) X h6 Xf h6f φf δ δf hXf hδf
  have e2 := t.baseChange R (Localization.Away f) (IsScalarTower.toAlgHom R₀ R _) X h6 Xf h6f φf δ δf hXf hδf
  simp only [IsScalarTower.coe_toAlgHom'] at e1 e2
  rw [map_sub, ← e1, ← e2]
  exact sub_eq_zero.2 (hchart W hW Y ψ hY hgen _ g Xf χ hχ h6f δf)
end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicFormEqRationalPhaseKernelSeriesStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicForm_eq_rationalPhase_kernelSeries : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (t : D.ntw.Tw) (j : Fin D.R.m)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RatHyp T Rl F κ v₀ O t j hV →
  ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
  ∀ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) →
  ∀ ph : ℂ, IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph →
  ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) χ ξR ω φ,
    KerDat Rl.toRealDat j (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver Rl.toRealDat (Rl.mu v) (ownAt D v)) ω φ →
  ∀ h ∈ GfC (Vc D j), ∀ P ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) (fin (Vc D j) h)),
    ∃ x, adForm Rl.toRealDat j x (fun τ => u τ) = ph • singleSeries Rl.toRealDat j ω φ h (c0L j P) u := by
  first | exact @GlobalTheory.KerPhase.exists_adForm_eq_phase_smul | exact GlobalTheory.KerPhase.exists_adForm_eq_phase_smul | (intros; apply GlobalTheory.KerPhase.exists_adForm_eq_phase_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleSemiAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_symmetric_lineBundle_semiAbelian : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  first | exact @GlobalTheory.SymAmple.exists_ample_symmetric | exact GlobalTheory.SymAmple.exists_ample_symmetric | (intros; apply GlobalTheory.SymAmple.exists_ample_symmetric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisIntKQ
section
open Matrix GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.BCFL
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.IntBasisKQ
open ReciprocityTheory.DiscreteGroups.LocalClassField

variable (p : ℕ) [Fact p.Prime]

theorem exists_basis_OK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ (ι : Type) (_ : Fintype ι) (β : Module.Basis ι ℚ_[p] K),
      ∀ x : K, x ∈ OK p K ↔ ∀ i, ‖β.repr x i‖ ≤ 1 := by
  letI := zpAlgOK p K
  haveI := isScalarTower_zp_OK p K
  haveI := isIntegralClosure_OK p K
  haveI := isTorsionFree_zp_K p K
  haveI : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  haveI : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (OK p K) (nonZeroDivisors ℤ_[p])) K :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (OK p K)
  let β₀ := Module.finBasis ℤ_[p] (OK p K)
  let β := β₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K
  refine ⟨_, inferInstance, β, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have e : x = algebraMap (OK p K) K ⟨x, hx⟩ := rfl
    rw [e, Module.Basis.localizationLocalization_repr_algebraMap]
    exact (β₀.repr ⟨x, hx⟩ i).2
  · let z : _ → ℤ_[p] := fun i => ⟨β.repr x i, hx i⟩
    have hx' : x = algebraMap (OK p K) K (∑ i, z i • β₀ i) := by
      conv_lhs => rw [← β.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℤ_[p] (OK p K) K,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, ← Module.Basis.localizationLocalization_apply ℚ_[p]
        (nonZeroDivisors ℤ_[p]) K]
      rfl
    rw [hx']
    exact (∑ i, z i • β₀ i).2

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

variable (p : ℕ) [Fact p.Prime]

section Tensor

variable {A B : Type} [CommRing A] [Algebra ℚ_[p] A] [CommRing B] [Algebra ℚ_[p] B]
  {ι κ : Type} [Fintype ι] [Fintype κ] (β : Module.Basis ι ℚ_[p] A) (γ : Module.Basis κ ℚ_[p] B)
  (OA : Subring A) (OB : Subring B)

def IntCoord (z : A ⊗[ℚ_[p]] B) : Prop := ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1

variable {p β γ}

theorem intCoord_add {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) :
    IntCoord p β γ (z + w) := fun k => by
  rw [map_add, Finsupp.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (hw k))

theorem intCoord_smul {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    IntCoord p β γ (c • z) := fun k => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hz k)

theorem intCoord_neg {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) : IntCoord p β γ (-z) := fun k => by
  rw [map_neg, Finsupp.neg_apply, norm_neg]
  exact hz k

theorem intCoord_zero : IntCoord p β γ (0 : A ⊗[ℚ_[p]] B) := fun k => by simp

theorem intCoord_sum {σ : Type} (s : Finset σ) (f : σ → A ⊗[ℚ_[p]] B) (h : ∀ t ∈ s, IntCoord p β γ (f t)) :
    IntCoord p β γ (∑ t ∈ s, f t) := by
  induction s using Finset.induction_on with
  | empty => simpa using intCoord_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intCoord_add (h a (Finset.mem_insert_self _ _)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

variable {OA OB}

theorem intCoord_tmul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {a : A} {b : B} (ha : a ∈ OA) (hb : b ∈ OB) : IntCoord p β γ (a ⊗ₜ[ℚ_[p]] b) := fun ⟨i, j⟩ => by
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ((hB b).1 hb j) (norm_nonneg _) ((hA a).1 ha i)

theorem basis_mem (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (i : ι) : β i ∈ OA :=
  (hA _).2 fun i' => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem intCoord_mul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) : IntCoord p β γ (z * w) := by
  set b := β.tensorProduct γ
  have e : z * w = ∑ k, ∑ l, (b.repr z k * b.repr w l) • (b k * b l) := by
    conv_lhs => rw [← b.sum_repr z, ← b.sum_repr w]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  rw [e]
  refine intCoord_sum _ _ fun k _ => intCoord_sum _ _ fun l _ => intCoord_smul ?_ ?_
  · obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := l
    simp only [b, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul]
    exact intCoord_tmul hA hB (OA.mul_mem (basis_mem hA i) (basis_mem hA i'))
      (OB.mul_mem (basis_mem hB j) (basis_mem hB j'))
  · rw [norm_mul]
    exact mul_le_one₀ (hz k) (norm_nonneg _) (hw l)

theorem mem_closure_iff (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    (z : A ⊗[ℚ_[p]] B) :
    z ∈ Subring.closure (Set.range (fun a : OA => (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) a) ∪
      Set.range (fun b : OB => (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) b)) ↔
      ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1 := by
  let S : Subring (A ⊗[ℚ_[p]] B) :=
    { carrier := {z | IntCoord p β γ z}
      mul_mem' := intCoord_mul hA hB
      one_mem' := intCoord_tmul hA hB OA.one_mem OB.one_mem
      add_mem' := intCoord_add
      zero_mem' := intCoord_zero
      neg_mem' := intCoord_neg }
  constructor
  · intro hz
    refine (Subring.closure_le (t := S)).2 (Set.union_subset ?_ ?_) hz
    · rintro _ ⟨a, rfl⟩
      exact intCoord_tmul hA hB a.2 OB.one_mem
    · rintro _ ⟨b, rfl⟩
      exact intCoord_tmul hA hB OA.one_mem b.2
  · intro hz
    rw [← (β.tensorProduct γ).sum_repr z]
    refine Subring.sum_mem _ fun ⟨i, j⟩ _ => ?_
    rw [Module.Basis.tensorProduct_apply, TensorProduct.smul_tmul',
      show ((β.tensorProduct γ).repr z (i, j) • β i) ⊗ₜ[ℚ_[p]] γ j =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) ((β.tensorProduct γ).repr z (i, j) • β i) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) (γ j) by
          rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, ?_⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, basis_mem hB j⟩, rfl⟩))
    refine (hA _).2 fun i' => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, norm_mul]
    refine mul_le_one₀ (hz (i, j)) (norm_nonneg _) ?_
    split_ifs <;> simp

end Tensor

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

theorem exists_basis_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℚ_[p] (KQ p K r)),
      ∀ x, x ∈ intKQ p K r ↔ ∀ i, ‖b.repr x i‖ ≤ 1 := by
  intro p _ K hK r hr
  obtain ⟨ι₁, _, β, hβ⟩ := exists_basis_OK p K hK
  obtain ⟨ι₂, _, γ, hγ⟩ := exists_basis_OK p (Qr p r)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr)
  refine ⟨ι₁ × ι₂, inferInstance, β.tensorProduct γ, fun x => ?_⟩
  exact mem_closure_iff (OA := GlobalTheory.LKLoc.intK p K) (OB := GlobalTheory.LKLoc.intR p (Q0 p) r) hβ hγ x

end GlobalTheory.IntBasisKQ
end
end

