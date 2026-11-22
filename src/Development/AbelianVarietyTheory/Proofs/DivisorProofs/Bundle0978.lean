import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0627
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLocallyGeneratedAffine
section
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.SecPowLoc

theorem fnOf_map {X : Scheme.{0}} [IsIntegral X] {U V : X.Opens} (i : V ⟶ U)
    (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (X.presheaf.map i.op a) = fnOf U (i.le h) a :=
  X.presheaf.germ_res_apply i _ h a

theorem exists_pow_regularAt_on {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X)
    (f : X.functionField) (t : Γ(X, ⊤)) (hf : ∀ z ∈ X.basicOpen t, D.RegularAt z f)
    (W : X.Opens) (hW : IsAffineOpen W) (g : X.functionFieldˣ) (hg : ∀ z ∈ W, D.IsEqn z g)
    {y : X} (hy : y ∈ W) (ht : genericPoint X ∈ X.basicOpen t) :
    ∃ n : ℕ, ∀ z ∈ W, D.RegularAt z (t ^ n • f) := by
  set t' : Γ(X, W) := X.presheaf.map (homOfLE le_top).op t
  have hB : X.basicOpen t' = W ⊓ X.basicOpen t := X.basicOpen_res t _
  have hgen : genericPoint X ∈ X.basicOpen t' := hB ▸ memInf (gen_mem hy) ht
  obtain ⟨b, hb⟩ := exists_fnOf_eq (f := f * (g : X.functionField)) hgen fun z hz => by
    rw [hB] at hz
    exact (hg z hz.1).regularAt_iff.1 (hf z hz.2)
  obtain ⟨n, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen X W hW t' b
  have key : fnOf W (gen_mem hy) a = fnOf ⊤ trivial t ^ n * (f * (g : X.functionField)) := by
    have e := congrArg (fnOf _ hgen) ha
    rw [map_mul, map_pow, hb] at e
    erw [fnOf_map, fnOf_map, fnOf_map] at e
    exact e
  refine ⟨n, fun z hz => (hg z hz).regularAt_iff.2 ?_⟩
  rw [Algebra.smul_def, algebraMap_top, map_pow, mul_assoc, ← key]
  exact regAt_fnOf hz _ a

end GlobalTheory.Cartier.SecPowLoc

namespace GlobalTheory.Cartier

open SecPowLoc in

theorem exists_smul_mem_sections_of_regAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D : CartierDiv X)
    (x : X) (g : X.functionFieldˣ), D.IsEqn x g → ∀ f : X.functionField, RegAt x (f * g) →
    ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧ s • f ∈ D.sections := by
  intro X _ _ D x g hg f hf
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  obtain ⟨U', hxU', a, ha⟩ := hf.exists_fnOf
  obtain ⟨_, ⟨t, rfl⟩, hxt, htle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen X) (show x ∈ U ⊓ U' from ⟨hxU, hxU'⟩)
  have hft : ∀ z ∈ X.basicOpen t, D.RegularAt z f := fun z hz => by
    have h1 := regAt_fnOf (htle hz).2 (gen_mem hxU') a
    rw [ha] at h1
    exact (hU z (htle hz).1).regularAt_iff.2 h1
  have hgt : genericPoint X ∈ X.basicOpen t := gen_mem hxt
  have loc : ∀ y : X, ∃ W : X.Opens, y ∈ W ∧ ∃ n : ℕ, ∀ z ∈ W, D.RegularAt z (t ^ n • f) := by
    intro y
    obtain ⟨V, hyV, g', hg'⟩ := D.exists_isEqn_nhds y
    obtain ⟨W, hW, hyW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hyV
    exact ⟨W, hyW, exists_pow_regularAt_on D f t hft W hW g' (fun z hz => hg' z (hWV hz)) hyW hgt⟩
  choose W hyW n hn using loc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set X))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  refine ⟨t ^ (T.sup n + 1), ?_, mem_sections.2 fun z => ?_⟩
  · rw [X.basicOpen_pow t (Nat.succ_pos _)]
    exact hxt
  · obtain ⟨y, hyT, hz⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
    have hle : n y ≤ T.sup n + 1 := (Finset.le_sup hyT).trans (Nat.le_succ _)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    have h2 := (hn y z hz).regAt_mul (regAt_fnOf (U := ⊤) trivial trivial (t ^ (T.sup n + 1 - n y)))
    rwa [← algebraMap_top, ← Algebra.smul_def] at h2

end GlobalTheory.Cartier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalSpanRightInvariantOfTrivialInfinityFins
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem infGL_mem_supS {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ GlobalTheory.JSW.supS E a S := by
  intro w _
  have h := pFin_infGL (E := E) (a := a) y
  ext i j
  have := congrArg (fun z : GL (Fin a) (Af E) => (pLoc E w) ((z : Matrix (Fin a) (Fin a) (Af E)) i j)) h
  simpa [Matrix.one_apply, apply_ite] using this

theorem locSpan_rightInv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) (k : GA E a),
    GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) →
    (∀ g, F₀ (g * k) = F₀ g) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S F₀, ∀ g, F (g * k) = F g := by
  intro E _ _ _ a S F₀ k hInf hS hF₀
  let V : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ g, F (g * k) = F g}
      add_mem' := fun {F G} hF hG g => by simp only [Pi.add_apply, hF g, hG g]
      zero_mem' := fun _ => rfl
      smul_mem' := fun c F hF g => by simp only [Pi.smul_apply, hF g] }
  have hc : ∀ h ∈ GlobalTheory.JSW.supS E a S, h * k = k * h := fun h hh => GlobalTheory.T.adelicGL_complementary_supports_commute E a S h k hh hInf hS
  refine fun F hF => (locSpan_le (V := V) hF₀ ?_ ?_) hF
  · intro F hF h hh g
    show F (g * k * h) = F (g * h)
    rw [mul_assoc, ← hc h hh, ← mul_assoc, hF]
  · intro F hF X _ ν _ k' γ _ g
    show GlobalTheory.JSW.kerInf ν k' γ F (g * k) = GlobalTheory.JSW.kerInf ν k' γ F g
    unfold GlobalTheory.JSW.kerInf
    congr 1
    funext x
    rw [mul_assoc, ← hc _ (infGL_mem_supS S (γ x)), ← mul_assoc, hF]

end GlobalTheory.JSW.MirSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProofStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof : ContSt := by
  first | exact @GlobalTheory.IsoTriv.contSt_holds | exact GlobalTheory.IsoTriv.contSt_holds | (intros; apply GlobalTheory.IsoTriv.contSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegSpreadCore

theorem spMap_subtype_eq {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) :
    spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem spMap_inclusion_eq {S : Type} [CommRing S] {R₀ R₁ R₂ : Subring S} (h₁ : R₀ ≤ R₁) (h₂ : R₁ ≤ R₂) (h : R₀ ≤ R₂) :
    spMap (Subring.inclusion h) = spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem siegPB_spread_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ sE e hd hu
  classical
  obtain ⟨φd, φd₂, hφd, hsd, hwd, hld⟩ := hd
  obtain ⟨φu, φu₂, hφu, hsu, hwu, hlu⟩ := hu
  haveI := d₀.ab.smooth; haveI := d₀.ab.proper; haveI := u.ab.smooth; haveI := u.ab.proper
  have hZ : IsPullback (pullback.lift φu (e.A.hom ≫ spMap R₀.subtype) (by rw [hφu.1.w, Category.assoc]))
      e.A.hom (pullback.snd u.A.hom h₀) (spMap R₀.subtype) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback u.A.hom h₀)
    rw [pullback.lift_fst]; exact hφu.1
  obtain ⟨F₁, hF₁⟩ := GlobalTheory.T.baseChange_iso_spreads_to_subring S R₀ e.A.left d₀.A.left (pullback u.A.hom h₀) e.A.hom d₀.A.hom
    (pullback.snd u.A.hom h₀) φd _ hφd.1 hZ
  let R' : Subring S := Subring.closure ((R₀ : Set S) ∪ (F₁ : Set S))
  have hR0 : R₀ ≤ R' := fun x hx => Subring.subset_closure (Or.inl hx)
  have hF1 : (F₁ : Set S) ⊆ R' := fun x hx => Subring.subset_closure (Or.inr hx)
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R₀) (Sp R') s₀
    (spMap (Subring.inclusion hR0) ≫ s₀) (spMap (Subring.inclusion hR0)) d₀ rfl
  have hd'c := hd'
  obtain ⟨φ', φ'₂, hφ', hs', hw', hl'⟩ := hd'
  have eR' := spMap_subtype_eq hR0
  let j : e.A.left ⟶ d'.A.left := hφ'.1.lift φd (e.A.hom ≫ spMap R'.subtype)
    (by rw [hφd.1.w, eR', Category.assoc])
  have hj1 : j ≫ φ' = φd := hφ'.1.lift_fst _ _ _
  have hj2 : j ≫ d'.A.hom = e.A.hom ≫ spMap R'.subtype := hφ'.1.lift_snd _ _ _
  obtain ⟨ψZ, hψZ1, hψZ2⟩ := hF₁ R' hR0 hF1 d'.A.left d'.A.hom φ' j hφ'.1 hj1 hj2
  let ψ := ψZ ≫ pullback.fst u.A.hom h₀
  have hψ : IsPullback ψ d'.A.hom u.A.hom (spMap (Subring.inclusion hR0) ≫ h₀) :=
    hψZ2.paste_horiz (IsPullback.of_hasPullback _ _)
  have hjψ : j ≫ ψ = φu := by
    show j ≫ ψZ ≫ pullback.fst u.A.hom h₀ = φu
    rw [reassoc_of% hψZ1, pullback.lift_fst]
  have eh : spMap R'.subtype ≫ spMap (Subring.inclusion hR0) ≫ h₀ = spMap R₀.subtype ≫ h₀ := by
    rw [← Category.assoc, ← eR']
  have gj : IsGrpPullback e.A d'.A (spMap R'.subtype) j :=
    IsGrpPullback.cancel hφ' (by rw [hj1, ← eR']; exact hφd) hj2
  obtain ⟨j₂, hsj⟩ := GlobalTheory.SiegDesc.exists_isSquare hj2
  have hj₂ : j₂ ≫ φ'₂ = φd₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst d₀.A d₀.A).left = _ ≫ (fst d₀.A d₀.A).left
      rw [Category.assoc, hs'.1, ← Category.assoc, hsj.1, Category.assoc, hj1, hsd.1]
    · show (_ ≫ _) ≫ (snd d₀.A d₀.A).left = _ ≫ (snd d₀.A d₀.A).left
      rw [Category.assoc, hs'.2, ← Category.assoc, hsj.2, Category.assoc, hj1, hsd.2]
  have hwj : LBIso e.P (d'.P.pull j₂) := by
    rw [← hj₂] at hwd
    exact (hwd.trans e.isLB (pull_isLB d₀.isLB _) (pull_isLB (pull_isLB d₀.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull d₀.isLB φ'₂ j₂).symm).trans e.isLB
      (pull_isLB (pull_isLB d₀.isLB _) _) (pull_isLB d'.isLB _) (GlobalTheory.SiegelPullComp.iso_pull j₂ hw').symm
  have hlj : ∀ a, (e.lev a).left ≫ j = spMap R'.subtype ≫ (d'.lev a).left := by
    intro a
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hj1, hld a, Category.assoc, hl' a, ← Category.assoc, ← eR']
    · have a₁ : (e.lev a).left ≫ e.A.hom = 𝟙 _ := Over.w (e.lev a)
      have a₂ : (d'.lev a).left ≫ d'.A.hom = 𝟙 _ := Over.w (d'.lev a)
      rw [Category.assoc, hj2, reassoc_of% a₁, Category.assoc, a₂]
      simp
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ gj (by rw [eh, hjψ]; exact hφu)
  obtain ⟨F₃, hF₃⟩ := GlobalTheory.T.lbIso_spread_alt g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ j₂ φu₂ gj.1 hsj hwj
    (by rw [hjψ]; exact hsu) hwu
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.T.siegel_level_sections_spread_to_subring g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ hlj
    (fun a => by rw [eh, hjψ]; exact hlu a)
  refine ⟨F₁ ∪ F₂ ∪ F₃ ∪ F₄, fun R₁ hle hF s₁ d₁ hd₁ => ?_⟩
  have hsub : ∀ G : Finset S, G ⊆ F₁ ∪ F₂ ∪ F₃ ∪ F₄ → (G : Set S) ⊆ R₁ :=
    fun G h => (Finset.coe_subset.2 h).trans hF
  have hR'1 : R' ≤ R₁ := Subring.closure_le.2 (Set.union_subset hle
    (hsub F₁ (by intro x; simp only [Finset.mem_union]; tauto)))
  have eR1 := spMap_inclusion_eq hR0 hR'1 hle
  have hd₁' : SiegPB d₁ d' (spMap (Subring.inclusion hR'1)) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd'c (by rw [← eR1]; exact hd₁)
  obtain ⟨φ₁, φ₁₂, hφ₁, hs₁, hw₁, hl₁⟩ := hd₁'
  have gm := hF₂ R₁ hR'1 (hsub F₂ (by intro x; simp only [Finset.mem_union]; tauto)) d₁.A φ₁ hφ₁
  have e2 : spMap (Subring.inclusion hR'1) ≫ spMap (Subring.inclusion hR0) ≫ h₀ =
      spMap (Subring.inclusion hle) ≫ h₀ := by rw [eR1, Category.assoc]
  rw [e2] at gm
  obtain ⟨χ₂, hχ⟩ := GlobalTheory.SiegDesc.exists_isSquare gm.1.w
  refine ⟨φ₁ ≫ ψ, χ₂, gm, hχ, hF₃ R₁ hR'1 (hsub F₃ (by intro x; simp only [Finset.mem_union]; tauto))
    s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁.1 hs₁ hw₁ hχ, fun a => ?_⟩
  have := hF₄ R₁ hR'1 (hsub F₄ (by intro x; simp only [Finset.mem_union]; tauto)) s₁ d₁ φ₁
    (by rw [e2]; exact gm) hl₁ a
  rw [e2] at this
  exact this

end GlobalTheory.SiegSpreadCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigKQFixedEqInclK
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem frobQ_fixed_mem (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (b : Qr p r) (hb : frobQ p r b = b) :
    ∃ c : ℚ_[p], algebraMap ℚ_[p] (Qr p r) c = b := by
  have h1 : frobK p (Q0 p) (b : PadicAlgCl p) = b := congrArg Subtype.val hb
  have h2 : (b : PadicAlgCl p) ∈ Q0 p := mem_of_frobK_fixed inferInstance (Kn_le_Kur hr b.2) h1
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 h2
  exact ⟨c, Subtype.ext hc⟩

theorem sigKQ_fixed_eq_inclK : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ x : GlobalTheory.LKRes.KQ p K r, GlobalTheory.LKRes.sigKQ p K r x = x → ∃ a : K, GlobalTheory.LKRes.inclK p K r a = x := by
  intro p _ K r hr
  change ∀ x : K ⊗[ℚ_[p]] Qr p r, Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) x = x →
    ∃ a : K, (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] Qr p r) a = x
  intro x hx
  let f : ℚ_[p] →ₗ[ℚ_[p]] Qr p r := Algebra.linearMap _ _
  let g : Qr p r →ₗ[ℚ_[p]] Qr p r := (frobQ p r).toLinearMap - LinearMap.id
  have hex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : frobQ p r b = b := sub_eq_zero.1 hb
      exact frobQ_fixed_mem p r hr b hb'
    · rintro ⟨c, rfl⟩
      simp [g, f]
  have hex2 := Module.Flat.lTensor_exact K hex
  have hg : g.lTensor K =
      (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)).toLinearMap - LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [g, TensorProduct.tmul_sub]
  have hx0 : g.lTensor K x = 0 := by
    rw [hg, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    exact sub_eq_zero.2 hx
  obtain ⟨y, hy⟩ := (hex2 x).1 hx0
  refine ⟨TensorProduct.rid ℚ_[p] K y, ?_⟩
  rw [← hy]
  clear hy hx hx0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, f, Algebra.linearMap_apply]
    change (c • a) ⊗ₜ[ℚ_[p]] (1 : Qr p r) = a ⊗ₜ[ℚ_[p]] (algebraMap ℚ_[p] (Qr p r) c)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, map_add]

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingletonStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n → Subsingleton (Ht q (sp B) n i) := by
  first | (exact @GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (exact GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (intros; apply GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologyTwoSubsingleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ, Subsingleton (Ht q (sp B) 2 i) := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (exact GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix Filter Topology

noncomputable section

namespace GlobalTheory.CuspRep.TailFix

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem entry_int {w : HeightOneSpectrum (𝓞 E)} {g : GL (Fin a) (w.adicCompletion E)} (hg : g ∈ KGL w a)
    (i j : Fin a) : g i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨h, rfl⟩ := hg
  exact (h i j).2

theorem tendsto_of_loc {α : Type} {l : Filter α} {f : α → Af E} {x : Af E}
    (hx : ∀ v, pLoc E v x ∈ v.adicCompletionIntegers E) (hf : ∀ b v, pLoc E v (f b) ∈ v.adicCompletionIntegers E)
    (h : ∀ v, ∀ᶠ b in l, pLoc E v (f b) = pLoc E v x) : Tendsto f l (𝓝 x) := by
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : ∀ y : Af E, (∀ v, pLoc E v y ∈ v.adicCompletionIntegers E) →
      ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletionIntegers E : Set (v.adicCompletion E)) :=
    fun y hy v => ⟨pLoc E v y, hy v⟩
  have hl : ∀ y hy, s (lift y hy) = y := fun y hy => FiniteAdeleRing.ext _ fun v => rfl
  have h1 : Tendsto (fun b => lift (f b) (hf b)) l (𝓝 (lift x hx)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| (h v).mono fun b hb => Subtype.ext hb.symm
  have h2 := (hs.tendsto _).comp h1
  rw [hl] at h2
  exact h2.congr fun b => hl _ _

theorem exists_tail {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 (1 : GL (Fin a) (Af E))) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 E)), ∀ r : GL (Fin a) (Af E),
      (∀ v, GeneralLinearGroup.map (pLoc E v) r ∈ KGL v a) →
      (∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) r = 1) → r ∈ U := by
  classical
  by_contra hn
  push_neg at hn
  choose r hr1 hr2 hrU using hn
  have ent : ∀ q : Finset (HeightOneSpectrum (𝓞 E)) → GL (Fin a) (Af E),
      (∀ F v, GeneralLinearGroup.map (pLoc E v) (q F) ∈ KGL v a) →
      (∀ F, ∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) (q F) = 1) →
      Tendsto (fun F => (q F).val) atTop (𝓝 1) := fun q hq1 hq2 =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (fun v => by rw [Matrix.one_apply]; split_ifs <;> simp)
        (fun F v => entry_int (hq1 F v) i j) fun v => by
        filter_upwards [eventually_ge_atTop {v}] with F hF
        have e := hq2 F v (hF (Finset.mem_singleton_self v))
        rw [← map_one (GeneralLinearGroup.map (pLoc E v))] at e
        exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) e
  have ht : Tendsto r atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent r hr1 hr2).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
      (ent (fun F => (r F)⁻¹) (fun F v => by rw [map_inv]; exact inv_mem (hr1 F v))
        (fun F v hv => by rw [map_inv, hr2 F v hv, inv_one])))
  obtain ⟨F, hF⟩ := (ht.eventually hU).exists
  exact hrU F hF

end GlobalTheory.CuspRep.TailFix

open GlobalTheory.CuspRep.TailFix in

theorem GlobalTheory.CuspRep.fixed_of_locFixed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)),
    (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E),
    (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a) →
    (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  classical
  intro E _ _ _ a φ hφ S hS k hk1 hk2
  have hU : {x : GL (Fin a) (Af E) | finRep E a x φ = φ} ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
    hφ.level.mem_nhds (by simp)
  obtain ⟨F, hF⟩ := exists_tail hU
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a) →
      (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∀ w ∈ F, w ∉ T → GeneralLinearGroup.map (pLoc E w) k = 1) → finRep E a k φ = φ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k h1 h2 h3
      refine hF k (fun v => ?_) (fun v hv => h3 v hv (by simp))
      by_cases hv : v ∈ S
      · rw [h2 v hv]; exact one_mem _
      · exact h1 v hv
    | insert w T hw ih =>
      intro k h1 h2 h3
      obtain ⟨g, hg⟩ : ∃ g, g = locGL E a w (GeneralLinearGroup.map (pLoc E w) k) := ⟨_, rfl⟩
      have hgH : finRep E a g φ = φ := by
        by_cases hwS : w ∈ S
        · rw [hg, h2 w hwS, map_one, map_one]; rfl
        · rw [hg]; exact hS w hwS _ (h1 w hwS)
      have e : ∀ v, GeneralLinearGroup.map (pLoc E v) (g⁻¹ * k) =
          if v = w then 1 else GeneralLinearGroup.map (pLoc E v) k := fun v => by
        rw [map_mul, map_inv]
        split_ifs with hv
        · subst hv; rw [hg, pLoc_locGL, inv_mul_cancel]
        · rw [hg, pLoc_locGL_of_ne hv, inv_one, one_mul]
      have hk' : finRep E a (g⁻¹ * k) φ = φ := by
        refine ih _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv hvT => ?_)
        · rw [e]; split_ifs
          · exact one_mem _
          · exact h1 v hv
        · rw [e]; split_ifs
          · rfl
          · exact h2 v hv
        · rw [e]; split_ifs with h
          · rfl
          · exact h3 v hv (by simp [h, hvT])
      calc finRep E a k φ = finRep E a (g * (g⁻¹ * k)) φ := by rw [mul_inv_cancel_left]
        _ = φ := by rw [map_mul, Module.End.mul_apply, hk', hgH]
  exact key F k hk1 hk2 (fun w hw hwF => absurd hw hwF)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
section
noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct ContDiff

namespace GlobalTheory.HolRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def NegFirst (V : HSp D) (q : ℕ) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ ρ, (x ρ)ᴴ * gramAt D V ρ * x ρ = diagonal fun c : Fin V.rank => if (c : ℕ) < q then (-1 : ℂ) else 1

def SmoothReal (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def IsHolFor (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : D.what₂.Tau → Fin V.rank → ℤ) (φ : GA D V → ℂ) : Prop :=
  SmoothReal θ V φ ∧
  (∀ ρ (c d : Fin V.rank), c < d → RderC θ V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹) φ = 0) ∧
  ∀ ρ (t : Fin V.rank → ℝ) g,
    φ (g * atTau θ V ρ (x ρ * diagonal (fun c => Complex.exp ((t c : ℂ) * Complex.I)) * (x ρ)⁻¹)) =
      Complex.exp (((∑ c, (w ρ c : ℝ) * t c : ℝ) : ℂ) * Complex.I) * φ g

def IsUnitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def unitLie {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : Set (Frame X.Ψ r) :=
  {Z | ∀ τ : X.Ψ, (mat Z τ)ᴴ * (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) +
    (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * mat Z τ = 0}

def expFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) : Frame Ψ r :=
  fun τ => (NormedSpace.exp (mat Z τ) : Matrix (Fin r) (Fin r) ℂ)

open Classical in

def unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) : Frame Ψ r :=
  fun τ' a b => if τ' = τ ∧ a = c ∧ b = d then 1 else 0

def ModelOf (V : HSp D) {r : ℕ} (hr : V.rank = r) (X : Data D.host.E r) : Prop :=
  (∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧ ModelW V hr X

def FrIs (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (u : GA D V) (y : Frame X.Ψ r) : Prop :=
  ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ →
    mat y τ = Matrix.reindex (finCongr hr) (finCongr hr) (archM V (θ ρ) u * x ρ)

def BaseDict (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    {Comp : Type} (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  (∀ k, ModelOf V hr (X k) ∧ NegFirst V (X k).p0 x₀ ∧ ∃ g, (dict g).1 = k) ∧
  (∀ h, ∃ γ ∈ GQ V, FrIs θ V hr (X (dict h).1) x₀ (γ * h) (dict h).2 ∧
    ∀ u ∈ GinfC V, ∃ γ' ∈ (X (dict h).1).Γ, ∃ y : Frame (X (dict h).1).Ψ r,
      dict (h * u) = ⟨(dict h).1, lact γ' y⟩ ∧ FrIs θ V hr (X (dict h).1) x₀ (γ * h * u) y) ∧
  ∀ g g', (∃ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩) →
    ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k

def KillPair {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : Prop :=
  (ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a) ∨ (ε a ≠ ε b ∧ b < a)

def wtCol {R : Ranks} (h : HCParam R) (p q c : ℕ) : ℤ :=
  ⌊if c < q then Formalism.L2.NTheta.lamAt h (p + c) - (p : ℚ) / 2 - ((q : ℚ) - 1) / 2 + (c : ℚ)
    else Formalism.L2.NTheta.lamAt h (c - q) + (q : ℚ) / 2 - ((p : ℚ) - 1) / 2 + ((c - q : ℕ) : ℚ)⌋

end GlobalTheory.HolRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelfStatement
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedExtFrobenius_iterate_degree_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKLoc.frobR_iterate_self | exact GlobalTheory.LKLoc.frobR_iterate_self | (intros; apply GlobalTheory.LKLoc.frobR_iterate_self <;> assumption)
end

