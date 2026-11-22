import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibre

theorem one_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_push h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

theorem comp_pow_pt {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (f : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end GlobalTheory.KerKilledFibre

namespace GlobalTheory.KerKilledFibre

theorem fibreKilled_of_base : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  intro d S' _ G _ _ P _ hP _ _ _ T g A' _ _ φ φ₂ P' hpb hsq hP' hiso _ H t T' x hT' hgen
  obtain ⟨f, hf⟩ := hT'
  obtain ⟨c, hc⟩ := hgen
  let r : Spec (T.residueField t) ⟶ Spec (S'.residueField (g.base t)) := Spec.map (g.residueFieldMap t)
  have hr : r ≫ S'.fromSpecResidueField (g.base t) = T.fromSpecResidueField t ≫ g :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t
  let p1 : pullback f r ⟶ T'.left := pullback.fst f r
  let p2 : pullback f r ⟶ Spec (T.residueField t) := pullback.snd f r
  let T'' : Over T := Over.mk (p2 ≫ T.fromSpecResidueField t)
  have hw : p1 ≫ T'.hom = T''.hom ≫ g := by
    show p1 ≫ T'.hom = (p2 ≫ T.fromSpecResidueField t) ≫ g
    rw [hf, ← Category.assoc, pullback.condition, Category.assoc, hr, Category.assoc]
  have hxw : (p1 ≫ x.left) ≫ G.hom = T''.hom ≫ g := by rw [Category.assoc, Over.w x]; exact hw
  let x'' : T'' ⟶ A' := Over.homMk (hpb.1.lift (p1 ≫ x.left) T''.hom hxw) (hpb.1.lift_snd _ _ _)
  have hx''φ : x''.left ≫ φ = p1 ≫ x.left := hpb.1.lift_fst _ _ _

  let Y : Over S' := Over.mk ((A' ⊗ T'').hom ≫ g)
  let a : Y ⟶ G := Over.homMk ((fst A' T'').left ≫ φ) (by
    show ((fst A' T'').left ≫ φ) ≫ G.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hpb.1.w, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (fst A' T'')))
  let b : Y ⟶ T' := Over.homMk ((snd A' T'').left ≫ p1) (by
    show ((snd A' T'').left ≫ p1) ≫ T'.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hw, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (snd A' T'')))
  let m := (lift a b).left
  let ψ := (lift (snd G T' ≫ x) (fst G T')).left
  let ψ'' := (lift (snd A' T'' ≫ x'') (fst A' T'')).left
  have heq : ψ'' ≫ φ₂ = m ≫ ψ := by
    have k1 : ψ ≫ (fst G G).left = (snd G T' ≫ x).left := by rw [← Over.comp_left, lift_fst]
    have k2 : ψ'' ≫ (fst A' A').left = (snd A' T'' ≫ x'').left := by rw [← Over.comp_left, lift_fst]
    have k3 : m ≫ (snd G T').left = b.left := by rw [← Over.comp_left, lift_snd]
    have k4 : ψ ≫ (snd G G).left = (fst G T').left := by rw [← Over.comp_left, lift_snd]
    have k5 : ψ'' ≫ (snd A' A').left = (fst A' T'').left := by rw [← Over.comp_left, lift_snd]
    have k6 : m ≫ (fst G T').left = a.left := by rw [← Over.comp_left, lift_fst]
    apply Over.tensorObj_ext
    · show ψ'' ≫ φ₂ ≫ (fst G G).left = m ≫ ψ ≫ (fst G G).left
      rw [hsq.1, reassoc_of% k2, k1]
      simp only [Over.comp_left, Category.assoc]
      rw [reassoc_of% k3, hx''φ]
      show _ = ((snd A' T'').left ≫ p1) ≫ x.left
      rw [Category.assoc]
    · show ψ'' ≫ φ₂ ≫ (snd G G).left = m ≫ ψ ≫ (snd G G).left
      rw [hsq.2, reassoc_of% k5, k4, k6]
      rfl
  obtain ⟨w, hwg⟩ := hiso
  obtain ⟨c1, hc1⟩ := gen_chartPull
    (chartPullSame P (fun _ : PUnit => ψ'' ≫ φ₂) (fun _ => ψ) (fun _ => 1) m (fun _ => heq)) c hc
  obtain ⟨c2, hc2⟩ := exists_down ((isGen_iff w).1 hwg) hP hP' (φ' := fun _ : PUnit => ψ'')
    (ε := fun _ => 1) c1 hc1
  have hx'' : x'' ^ d = 1 := H T'' x'' ⟨c2, hc2⟩

  let ρ : Over.mk (T''.hom ≫ g) ⟶ T' := Over.homMk p1 hw
  have hρ : (ρ ≫ x).left = x''.left ≫ φ := hx''φ.symm
  have e1 : ((ρ ≫ x) ^ d).left = (1 : Over.mk (T''.hom ≫ g) ⟶ G).left := by
    rw [pow_left_push hpb x'' (ρ ≫ x) hρ d, hx'', one_left_push hpb T'']
  have e2 : p1 ≫ (x ^ d).left = p1 ≫ (1 : T' ⟶ G).left := by
    have := congrArg CommaMorphism.left ((comp_pow_pt ρ x d).trans
      ((Over.OverMorphism.ext e1).trans (MonObj.comp_one ρ).symm))
    exact this
  have : Flat r := inferInstance
  have : Surjective r := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi p1 := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi p1).1 e2)

end GlobalTheory.KerKilledFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessOfClosedSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KernelRepFinite

theorem isClosedImmersion_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} (k : A ⟶ B)
    [IsClosedImmersion k.left] : IsClosedImmersion ((Over.pullback f).map k).left := by
  exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f k inferInstance

theorem lbIso_diag {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) {P : LB (G2 A).left} (hP : P.IsLB) :
    LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) := by
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [GlobalTheory.DiagAmpleBC.diag_comp A B β β₂ hs] at e₁
  exact LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm

theorem isFinite_restrict : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  intro S' _ G _ _ P hA hP V₀ hV hRel Z i hi hZ
  haveI : IsNoetherianRing Γ(S', V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV⟩
  let t : Sp Γ(S', V₀) ⟶ V₀.toScheme := hV.isoSpec.inv
  let GV := (Over.pullback V₀.ι).obj G
  let B := (Over.pullback t).obj GV
  have hAV : IsAbelianScheme GV := GlobalTheory.isAbelianScheme_pullback_obj _ G hA
  have hAB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj _ GV hAV
  let PV := P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)
  have hPV : PV.IsLB := pull_isLB hP _
  have h₁ := Pdiv.PullbackComparison.isGrpPullback V₀.ι G
  have h₂ := Pdiv.PullbackComparison.isGrpPullback t GV
  have hRelB : Out.RelAmple B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) :=
    GlobalTheory.DiagAmpleBC.relAmple_diag_pull _ _ GV hAV PV hPV hRel t B (Pdiv.PullbackComparison.pφ t GV)
      (Pdiv.PullbackComparison.pφ₂ t GV) h₂.1 (Pdiv.PullbackComparison.isSquare t GV)
  obtain ⟨ZL, iL, hiL, hfinL, -, hrep⟩ := GlobalTheory.kernelFiniteFlat_holds _ B hAB _
    (pull_isLB (pull_isLB hPV _) _) hRelB
  let ZV := (Over.pullback V₀.ι).obj Z
  let ZB := (Over.pullback t).obj ZV
  let iV : ZV ⟶ GV := (Over.pullback V₀.ι).map i
  let iB : ZB ⟶ B := (Over.pullback t).map iV
  have hmem : GlobalTheory.MemKL B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) iB := by
    refine GlobalTheory.memKL_of_push h₂ (pull_isLB hPV _) (pull_isLB (pull_isLB hPV _) _)
      (lbIso_diag GV B _ _ (Pdiv.PullbackComparison.isSquare t GV) hPV) iB ?_
    refine GlobalTheory.memKL_of_push h₁ (pull_isLB hP _) (pull_isLB hPV _)
      (lbIso_diag G GV _ _ (Pdiv.PullbackComparison.isSquare V₀.ι G) hP) _ ?_
    let zz : Over.mk ((ZB.hom ≫ t) ≫ V₀.ι) ⟶ Z :=
      Over.homMk (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) (by
        show (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ Z.hom = (pullback.snd ZV.hom t ≫ t) ≫ V₀.ι
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        congr 1
        exact pullback.condition)
    have e : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₁.1.w (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₂.1.w iB) = zz ≫ i := by
      apply Over.OverMorphism.ext
      show (iB.left ≫ Pdiv.PullbackComparison.pφ t GV) ≫ Pdiv.PullbackComparison.pφ V₀.ι G =
        (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ i.left
      simp only [Pdiv.PullbackComparison.pφ]
      rw [Pdiv.PullbackComparison.pullback_map_left_fst' t iV, Category.assoc,
        Pdiv.PullbackComparison.pullback_map_left_fst' V₀.ι i, Category.assoc]
    rw [e]
    apply hZ
    rintro _ ⟨y, rfl⟩
    show (((ZB.hom ≫ t) ≫ V₀.ι).base y) ∈ V₀
    exact (Scheme.Opens.range_ι V₀).subset ⟨(ZB.hom ≫ t).base y, rfl⟩
  obtain ⟨z, hz⟩ := (hrep ZB iB).1 hmem
  haveI : IsClosedImmersion iV.left := isClosedImmersion_pullback_map _ i
  haveI : IsClosedImmersion iB.left := isClosedImmersion_pullback_map _ iV
  have hz' : z.left ≫ iL.left = iB.left := congrArg (fun q => q.left) hz
  haveI : IsClosedImmersion (z.left ≫ iL.left) := by rw [hz']; infer_instance
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left iL.left
  have hZB : IsFinite ZB.hom := by
    rw [← Over.w z]; infer_instance
  have hV' : IsFinite ZV.hom := by
    have ec : ZV.hom = inv (pullback.fst ZV.hom t) ≫ pullback.snd ZV.hom t ≫ t := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [ec]
    haveI : IsFinite (pullback.snd ZV.hom t) := hZB
    infer_instance
  rw [← (isPullback_morphismRestrict Z.hom V₀).flip.isoPullback_hom_snd]
  haveI : IsFinite (pullback.snd Z.hom V₀.ι) := hV'
  infer_instance

end GlobalTheory.KernelRepFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntOfIntegralSchemeGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.IntFlat

theorem flat_of_generic_zero : ∀ {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of ℤ)) (x : X), (s x).asIdeal = ⊥ → Flat s := by
  intro X _ s x hx
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) X.affineOpenCover.openCover fun i => ?_
  let R := X.affineOpenCover.X i
  let j : Spec R ⟶ X := X.affineOpenCover.f i
  have : IsOpenImmersion j := X.affineOpenCover.map_prop i
  change Flat (j ≫ s)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ s)
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.bot_prime⟩
  have hg : genericPoint X ∈ Set.range j :=
    (genericPoint_specializes (j (Classical.arbitrary (Spec R)))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hg
  have h1 : p0 ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have h2 : j p0 ⤳ x := hq ▸ (h1.map j.continuous) |>.trans (genericPoint_specializes x)
  have h3 : (j ≫ s) p0 ⤳ s x := h2.map s.continuous
  have h4 : ((j ≫ s) p0).asIdeal ≤ ⊥ := hx ▸ (PrimeSpectrum.le_iff_specializes _ _).2 h3
  rw [← hφ] at h4
  have hinj : Function.Injective φ.hom := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    have : n ∈ ((Spec.map φ) p0).asIdeal := by
      show n ∈ Ideal.comap φ.hom ⊥
      simp [hn]
    simpa using h4 this
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  have : CharZero R := charZero_of_injective_algebraMap (e ▸ hinj)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

end GlobalTheory.IntFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOffVarietyMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem dvd_pair (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k n : ℕ) (hk0 : k ≠ 0) (hck : c ∣ k ^ 2)
    (hkn : (k : ℤ) ^ 2 ∣ n) (hsim : ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ x, ∃ y z, h n y = k • x + n • z) (x v : D.La) :
    (k : ℤ) ∣ ((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v := by
  obtain ⟨y, z, hyz⟩ := hon v
  have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast Nat.div_mul_cancel hck
  have h1 : D.EF (h n x) (h n y) = (k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z := by
    rw [hyz, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  have h2 := hsim x y
  rw [h1] at h2

  have h3 : (k : ℤ) ^ 2 ∣ (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v) := by
    have e1 : (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v)
        = ((k ^ 2 / c : ℕ) : ℤ) * ((k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z - c * u n * D.EF x y)
          - ((k ^ 2 / c : ℕ) : ℤ) * n * D.EF (h n x) z + (k : ℤ) ^ 2 * (u n * D.EF x y) := by
      rw [← hmZ]; ring
    rw [e1]
    refine dvd_add (dvd_sub (Dvd.dvd.mul_left (hkn.trans h2) _) ?_) (dvd_mul_right _ _)
    exact (hkn.trans (dvd_mul_left _ _)).mul_right _
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
  rw [pow_two] at h3
  exact (mul_dvd_mul_iff_left hkZ).1 h3

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem sqrt_hecke_point_weil_orthogonal (I : TateIsoO D K Q act e) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ)
    (c k N : ℕ) (hk : k.Coprime p) (hN : 0 < N) (hNp : N.Coprime p) (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) (x : D.La) :
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
      (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  have hp : p.Prime := Fact.out
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hL : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
  have gen : ∀ M j t : ℕ, 0 < M → k ∣ M → (N * k * M).Coprime p → 2 * j = M + t * (k * M) →
      ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
        (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
    intro M j t hM hkM hcop hj
    have hn' : 0 < N * k * M := Nat.mul_pos hL hM
    obtain ⟨M', rfl⟩ := hkM
    have hkn : (k : ℤ) ^ 2 ∣ ((N * k * (k * M') : ℕ) : ℤ) := ⟨N * M', by push_cast; ring⟩
    refine ⟨N * k * (k * M'), I.ev (N * k * (k * M')) (j • N • h (N * k * (k * M')) x), hn', hcop, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := (hcomp (N * k) (k * M') hL hM hcop).1 x
      have e1 : 2 • j • N • h (N * k * (k * M')) x
          = (k * M') • (N • h (N * k * (k * M')) x) + (N * k * (k * M')) • (t • h (N * k * (k * M')) x) := by
        simp only [smul_smul, ← add_smul]
        congr 1
        calc 2 * (j * N) = (2 * j) * N := by ring
          _ = _ := by rw [hj]; ring
      rw [← ev_nsmul, e1, I.add, (I.ker _ hn' hcop _).2 ⟨_, rfl⟩, _root_.mul_one, ev_nsmul,
        I.tower (N * k) (k * M') hL hM hcop, hz, smul_add, I.add, smul_comm N (N * k) z,
        (I.ker _ hL (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop) _).2 ⟨_, rfl⟩, _root_.mul_one]
    · rw [← ev_nsmul]
      refine pair_one I _ hn' hcop _ (fun v => ?_)
      obtain ⟨a, ha⟩ := dvd_pair h u c k _ hk0 hck hkn ((hsim _ hn' hcop).2) (hon _ hn' hcop) x v
      have e2 : 2 * D.EF ((k ^ 2 / c) • j • N • h (N * k * (k * M')) x) v
          = (2 * j : ℕ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h (N * k * (k * M')) x) v) := by
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
        push_cast; ring
      rw [e2, ha, hj]
      exact ⟨(1 + t * k) * a, by push_cast; ring⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hodd : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
        rw [hk] at h2; omega
      · exact h0
    obtain ⟨r, hr⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
    refine gen k (k * (r + 1)) 1 (Nat.pos_of_ne_zero hk0) dvd_rfl (Nat.Coprime.mul (Nat.Coprime.mul hNp hk) hk) ?_
    rw [hr]; ring
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h0 => hp2 h0.symm)
    refine gen (k * 2) k 0 (by positivity) (dvd_mul_right _ _)
      (Nat.Coprime.mul (Nat.Coprime.mul hNp hk) (Nat.Coprime.mul hk h2p)) ?_
    ring

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.HeckeAd

theorem fibre_triv (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ) (hk : k.Coprime p) (hN : 3 ≤ N) (hNp : N.Coprime p)
    (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (g : 𝟙_ (Over S) ⟶ o.A)
    (hg : g ∈ heckeSubA o (h (N * k)) N) (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) :
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).pull
      (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.UPel.HT.HeckeRootA.sqrt_hecke_point_weil_orthogonal I h u c k N hk (by omega) hNp hck hcomp hsim hon x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := GlobalTheory.HeckeFibre.transl_triv o.A o.ab _ (pull_isLB o.isLB _)
    (GlobalTheory.HeckeFibre.rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.PicBilin.triv_pow_of_translDiff o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y)
    (GlobalTheory.HeckeFibre.pic_field_eq_zero K) (o.eta (N • h (N * k) x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.UPel.HT.HeckeAd.KerPol

section Main
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ g)).left).Gen, t.IsGen) := by
  intro p _ D R _ b h u c k N hc hk hN hNp hck hlin hcomp hsim hon S s o g hg
  have hfib := fibre_triv p D R b h u c k N hk hN hNp hck hcomp hsim hon S s o g hg
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  set th : o.A ⟶ o.A := toUnit o.A ≫ g with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, GlobalTheory.UPel.HT.HeckeAd.pow_eq_one_of_mem o (h (N * k)) g hg, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.HeckeAd.KerPol
end Main
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermIdentityDescendsGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTerm_identity_descends_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  first | exact @GlobalTheory.TermDescend.main | exact GlobalTheory.TermDescend.main | (intros; apply GlobalTheory.TermDescend.main <;> assumption)
end

